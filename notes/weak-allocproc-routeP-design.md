# Route P design — an RVWMO-faithful per-hart STORE BUFFER in MachCSL with a lockstep replay

Design advisor (one-off, advisory: no proofs, no builds, no git/jj), 2026-10-19.  **Revised 2026-10-21 18:xx (rev 58 of the plan, no
review) by the reviser bringing §2.1/§2.4, §5–§8 up to date: THE SWITCH BRANCH P-M5–8 MERGED (`qxqznmnr`, 08:22; tip strict PASS 08:39) —
the registered machine IS route P (`xv6AccessDisc` := the twins, `MState.drvOkGuard` `MachCSL/Lang.lean:1300`, I3′/D17′); Q1 DONE (inc 1
`yywrnzvn`, [OWN.143] F1 `ovwowpkvwtuk`, Q1-c (E2) [OWN.144] `CapFetchOfs` 428/`CapFetchCyG` 642); rows 6h inc 1 (`G7FetchOwn` 113) + 6m
(`SbProg` 542: named `SailX`, NEW `FetchProg` F-6m-1) + 6d's data half (`CapDataTrap` 380/`CapDataOk` 486: named `cycReal` with `PC`)
LANDED; **the P-W6 spike `Weak/SbRealP.lean` 1,196 LANDED `wokqvokp` and FIRED kill criterion K2: F-PW6-1 — the registered machine lands
cross-hart same-byte plain stores in ISSUE order (`landBlockedForeign :1145` vs the twin's `wit1Run :1176`; `histOkP` `TsoMem.lean:900`,
`landFootOk` `Lang.lean:453`), STRONGER than RVWMO, because §2.1/§2.4's `pendOne` rule was NEVER implemented; F-PW6-2 DMA lands at once vs
the twin's buffered device rows → [OWN.148] gate; P-W6 re-estimated 3.2–6.7k** (`../xv6iris-weak-w2/PROGRESS-PW6.md` §3); the route
REOPENED [OWN.147] → advisory A6/B6/**A7** (`~/dev/weak-orch/weakmach/proposal-A7.md`) → **RULED [OWN.149] R-H**: the conformance matrix
(w2, plan row CM) → P-W6 with the walk input `IssueCo` + census and the [OWN.148] gate; the FAITHFUL STORE RULE R-PF′ (landing-time
placement via `Hist.insLanded` `TsoMem.lean:818`, 1.5–3.5k MachCSL) = G2-S item 0, FIRST after the capstone (plan row A6); K2′/K6;
**[OWN.150]** the S-R `DomAt` lift NOW (w3, plan row S-R; retires Q5–Q7/P-W3r-h/[OWN.112] if it lands, kill > 3k).  Spec audit
([OWN.140] → `notes/rvwmo-spec-audit.md`): [OWN.142] (R1) kept until the capstone, SAIL-GAP-1 (`notes/sail-gaps.md`); [OWN.143] `fence.i`
aligned (F1 landed), the DRAIN kept by [OWN.146] after F-143-1 (M-S2 after the capstone, plan row A7); the STRENGTHENING LEDGER (five rows:
`fence.i` drain, no ifetch forwarding, exclusive-read drain, no LB, issue-order landing) lives in the plan's REMAINING WORK section.
Σ remaining 11.6–26.6k (mid ≈ 19k), ≈ 89 % by lines (§7).  Rulings of the day [OWN.137]–[OWN.150] in §8.**  **Revised 2026-10-21 (rev 57 of the plan,
no review) by the reviser bringing §5–§7 up to date: the P-W3r sweep LANDED (seven of eight rows, 2,533 l.: `SbHoldX` 280 /
`SbHoldZero` 266 `wlroyyto`, `SbBlocked` 838 / `SbLbFree` 131 `kqsppmrw`, `SbVirtio` 407 `skyowwlm`, `SbHeldPin` 364 / `SbPteCust`
247 `xuorxlsx`; `Weak.lean:817-823`), row 6g `CapFrame` 588 + `SbOrdWalk.gatedW :597` (F-W2-V-1 (a)) `ozrqruqw`; row 6e → [OWN.136]
(queue row Q9); the [OWN.122] switch branch at CP-6z27 (RED 12; export flipped; measured +11.9k/−5.8k unmerged, 3.0–5.5k left —
§5 re-describes it from `../xv6iris-weak-w1/PROGRESS-W11F.md` §11); rulings [OWN.125]–[OWN.136] (supersessions: 128 WITHDRAWN,
130 → 134, 129/133 → 135) and [OWN.137]/[OWN.138] (row 6h, 2026-10-21: `fetchReplayOk`'s early E2/E3 half NAMED beside
`fetchLateChained` until A2 — REVISIT item 3; the (r1) own-hart arm 0.2–0.5k): **the ONLY named xv6 assumption is [OWN.131] — the
`DRIVER_OK` step guard, xv6 weak-memory bug #1 (`notes/xv6-weak-memory-bugs.md`)**; the REVISIT list = [OWN.124] (landed in `SbHoldX`'s
docstrings), (R2″) [OWN.116] until A4, [OWN.137] until A2.  Σ remaining 13.4–28.1k (mid ≈ 21k), ≈ 86 % by lines (§7).**  **Revised again 2026-10-19 (rev 56 of
the plan) by the reviser applying review R46 (`notes/weak-allocproc-plan-review-R46.md`, "the LOAD side of route P";
required changes [R46.1]–[R46.6], suggestions [R46.s1]–[R46.s4], 0 alt — every claim re-verified at the tip, `file:line`
below; one precision: the registered plain-read arm reads `tvn ≤ σ.top` at the tip (`MachCSL/Lang.lean:1708-1709`, the
eager/dual staging) and becomes `ltop` with the [OWN.122] switch) and the owner rulings [OWN.115]–[OWN.124]: **[OWN.123]
Q-R46-LOADSIDE = (P) — NO load buffer, in `SbCand` or in MachCSL; the replay's late landing replaces it**; **[OWN.124]
Q-R46-HH2 = (a) — `holding+0x12` exempt like `ip->ref`, carrying a `REVISIT [OWN.124]` flag** (§3.2, §3.4; alternative (b)
on file); [OWN.122] the MachCSL switch on a RED branch until P-M8 (§5).  Landed since rev 55 (all merged, strict
acceptance PASS): P-M1 `lrqroyvv`, P-M2 `uusvmmrl`, P-M3a+b `ouznrlqo`, P-M4a/b/c `uutlwtuz`; P-W2 (`Weak/SbWalk`/`SbAgree`/
`SbReplay`, 2,763 l.), P-W3 (`LitmusSbStuck`, `SbOrd` 1,269, `SbOrdWalk` 757, `LitmusSbStuck2`), P-W4 (`SbKill` 564),
`SbDevSt` 587, `SbHeadHop` 306, `SbHeadHop2` 551, 6b′ `CapRetag` 791, 6a `CapSync` 538 (`Weak.lean:804-818`).**  **Revised
2026-10-19 (rev 55 of the plan) by the reviser applying review R45 (`notes/weak-allocproc-plan-review-R45.md`; required changes [R45.1]–[R45.8],
suggestions [R45.s1]–[R45.s4]) and the owner rulings [OWN.111] (P re-confirmed after F-P1), [OWN.112] (Q-P-WFENCE-REF
= (a)), [OWN.113] (Q-P-FIFO = (b): per-address + fence-epoch buffer), [OWN.114] (Q-P-δ1 = (c): retire narrow δ1
inside P-M1); every R45 claim re-verified against the tip, `file:line` below; one alternative [R45.7-alt] (U2's
justification).**  Inputs: plan rev 54 (`notes/weak-allocproc-plan.md`), R44 PART 0 (§0.1–0.5, the (P) paragraph of
§0.4), `Weak/LitmusSBAcq.lean` (F44-1 machine-checked: `SBAcq.l1Cat :203`, `l1NoMember :611`, `l1MemberSrc :736`,
`l2cNo :548`), `Weak/LitmusSBAcqP.lean` (P0(b): `SBAcqP.uCat`/`uIoNo`/`uNoR1Ok`, `l1MemberP`, `l3Cat`/`l3NoMember`/
`l3MemberT`), the K spike (`notes/W10-K-spike.md` §6) and the K0 census (`notes/W10-K0-census.md` §3), the P0(a)
census (`notes/W10-P0a-wfence.md`), rulings [OWN.2] [OWN.105]–[OWN.114]; the tip read for this note: `MachCSL/Lang.lean`,
`TsoMem.lean`, `Resources.lean`, `Wp.lean`, `WpLock.lean`, `Lock.lean`, `Reserved.lean`, `WordHistDefs.lean`,
`KptInv.lean`, `Xv6/AccessDiscipline.lean` (ELEVEN conjuncts `:1106-1108`, `racyValOk :314`, `chainOkAt :327`,
`dynLockWinZAt :934`, `ksFrameAt :1027`), `Xv6/KernelImage.lean` (`ilock+0xe` = `0x80003360` `lw a5,8(a0)` → `blez`
at `+0x10`; `iunlock+0x1c` = `0x8000341c` `lw a5,8(s1)` → `blez` at `+0x1e`), `Weak/WeakAxiomatic.lean`,
`WeakMem.lean`, `SilCand.lean`, `SilOrd2.lean` (`enb :743`, `noStuckG :775`), `SilSite.lean` (`ruleOfIrefPos :207`),
`SilSiteTaint.lean` (`ruIlock`/`ruIunlock :647-650`), `SilSite.lean`, `SilKillT.lean`, `CertZ24.lean`, `CapF1.lean`,
`MachOfPf.lean` (`simStep :2874`, `machRunOfPfRun :2958`), `GraphFabResidue.lean`, `LockFacts.lean` (`relFenceBits
:97`, `relAdj :113`, `fenceCensus :137`), `tools/ci/roots.txt`, `roots-weak.txt`, `../xv6-riscv/kernel/fs.c:300,325`
(the two `ip->ref < 1` guards), `../xv6iris-weak-w1/PROGRESS-W11F.md` §6 + `MachCSL/SpikeP.lean` (P0(c), PASSED), `../xv6iris-weak-w3/
PROGRESS-P.md` + the merged `Weak/SbCand.lean`/`SbCandLit.lean` (P-W1, DONE).  Every size is an unverified estimate (ranges); every spec mark is w.r.t. riscv.cat /
RVWMO / Sail / Zifencei / PMAs.

## 0. Summary, and the three findings the owner has seen (F-P1 → [OWN.111]; F-R45-1 → [OWN.112]; F-HH2-1 → [OWN.124])

**[rev 56] The load side, settled ([OWN.121] → R46 → [OWN.123]).**  The owner asked whether route P also needs a logical
LOAD buffer ("it seems hard to build RVWMO without both the logical load buffer and store forwarding").  R46's answer,
ruled (P): a GENERAL operational RVWMO machine needs (i) a store side, (ii) a load side for R→R reordering — early
satisfaction or, equivalently, loads at STALE per-location views — and (iii) promises for R→W (load buffering, LB).
MachCSL has had (ii) in the view form since TSO and keeps it under P (a plain load reads at any view `tvn ∈ [tv, top]`
and raises only `rv` and the foreign-sourced `coh` floors, never `tv`: `MachCSL/Lang.lean:1708-1711`, `TsoMem.lean:356-358`;
`fence r,*` raises the floor to `rv`, `fencePost :491`); P adds (i); MachCSL-P lacks only (iii), and no RVWMO-consistent
GF of THIS binary has an LB shape (§1 row L6, §3.4 census).  **THIS proof needs no load buffer in the machine or in the
twin**: the replay walks each row in program order and reads the member's TOP; a load GF satisfied early is reproduced
by holding the competing store's LANDING back until the later-in-po read is realized (`land`'s `readersRealized`) —
same rf, same co, a different gmo witness, FAITHFUL for the quantifier.  Late landing can fail only when the EARLIER read
of the pair is itself a blocked head, i.e. a racy read whose GF source is a pending or unissued foreign store — a census
site (18 kernel pcs `SilSiteTab.kSites :71-96` + 8 device reads); that finite table (`SbOrd.HeadOrdRd :251`, §3.4) IS the
load-side analysis and had exactly ONE open row, **F-HH2-1 (`holding+0x12`) → [OWN.124] (a) with a REVISIT flag**.
MachCSL's stale views stay (they serve the Xv6 proofs) but the replay never uses them (member loads at `tvn = ltop`).

**FINDING F-HH2-1 (SbHeadHop2, w3 2026-10-19 16:27; → Q-R46-HH2, RULED [OWN.124] (a) + REVISIT).**  At a reachable walk
state hart z won the swap on `L` and its `sd a0,16(s1)` (`acquire+0x28`, `lk->cpu = mycpu()`) is pending; hart x in
`acquire(L)` → `holding` has realized `holding+0x0` (top 1 = GF 1) and its head `holding+0x12` (`0x80000c04`, `ld a5,16(a0)`)
reads GF's source = z's pending store ⇒ blocked.  x's next instructions `mv s1,a5; jal mycpu` → `mycpu`'s `sd ra,8(sp)`/`sd
s0,0(sp)` (`0x8000195e/60`) are WRITES, hence counted by the measure's `waitedOn` (`SbOrd.lean:171` `gisW`), and RVWMO
orders a `ld` before an unrelated `sd` by nothing (`PResidue` in the census), so `mu (.hd x)` may sit gmo-before z's store
and the (E5) edge does not descend.  Nothing is stuck (z's entry is landable); the MEASURE is too coarse — a load-side
proof artifact, the dual of the LB row.  Options: **(a) exempt `holding+0x12` like `ip->ref`** (a third `rdX` pc; both
values `≠ cpuAddr x`, so `holding` returns 0 on both sides; taint from `holding+0x12` across `jal mycpu` to the `seqz` at
`holding+0x1e`; 0.6–1.2k Weak, no new MachCSL record — the member-side value fact is already the export twin
`lkCpuReadAtP` `Xv6/AccessDiscipline.lean:1467`); (b) a custody-aware `waitedOn` (a write counts only if some other row
can wait on it) — structurally nicer but needs a NEW per-load MachCSL footprint record on the serial lane, 1.1–2.2k; (c)
name `noStuckP` — WEAKER.  **Ruling (a), "but this should be somehow flagged as something to look at again" ⇒ the
exemption carries `REVISIT [OWN.124]` in its Lean docstring, a row in the plan's REVISIT list (§D), the final theorem's
documentation (`LinkDiscAdequacy`/`RvwmoXv6Adequacy` header) names it, every status lists it; (b) stays on file.**  Both
(a) and (b) need the GF-side fact `HoldZero` (`SbHeadHop2.lean:479`), now a sized row ([R46.3], §3.4).

**The design in one paragraph.**  MachCSL keeps its timestamped byte histories, views and reservations; a plain
RAM store no longer appends at its instruction.  It is ISSUED into the hart's buffer (`MState.sb cpu`) and LANDS at
a later machine step (a new, always-enabled hart arm; the landing appends the store to the log at the then-top,
exactly as `MState.store` does today).  **The buffer is per-address + fence-epoch ([OWN.113] (b)): a pending store may
land once every OWN pending store that overlaps it (riscv.cat rule 1) or that was issued before the hart's last
`pw ∧ sw` fence (rule 4) has landed — exactly RVWMO's store side; the strict FIFO stays as the fallback instance of the
same `landOk` parameter until P0(c) measures the epoch case.**  Own loads (explicit and page-walker) forward per byte
from the buffer; a `fence` with pw and sr (`rw,rw`, `rw,r`, `w,rw`, `w,r`, `tso`), `fence.i`, an `.rl`/RCsc access and
any exclusive access to a buffered byte must wait for the drain; an `.aq` AMO does NOT drain and its write overtakes the
buffer.  The ghost memory the WP rules see is the MERGED history (own pending entries on top of the landed ones), keyed
by ISSUE stamps — so the store WP rules keep today's shape — and landing is ghost-invisible to clients: it only sets a
monotone side map `lp : stamp → Option Nat` (landing position), which views compare against.  On the Weak side the
twin candidate `SbCand` gets the same buffer; the walk is [OWN.106]'s step-by-step order with ONE uniform gate — *no
write may become the member-latest at a byte while a GF reader of its co-predecessor is unrealized, and no read is
replayed before its GF source is landed* — **with THREE exempt pcs ([OWN.112] (a), F-R45-1 §3.4; [OWN.124] (a), F-HH2-1
§0/§3.4, REVISIT-flagged): the two unlocked `ip->ref` reads (`ilock+0xe`, `iunlock+0x1c`) and `holding`'s `lk->cpu` read
(`holding+0x12`) are not gated; they read the landed top — provably ≥ 1 on both sides for `ip->ref`, provably `≠ cpuAddr x`
on both sides for `lk->cpu` — and run tainted until their compare (`blez` / `seqz`)** — which makes every other member read
return GF's value by construction.  Lockstep holds with no skips, no silent arm, no stale replay, NO load buffer
([OWN.123]) and no per-site value datum beyond those three pcs; the silent-AMO
twin, CertZ24–34, `SilSite*` premises and narrow δ1 are retired (δ1 DELETED inside P-M1, [OWN.114] (c)).  Progress
(`noStuckP`, §3.4 restated per [R45.2]) is now understood (confidence M, was M−); the merged-history ghost
(`interp_land`) was the riskiest MachCSL piece — **P0(c) PASSED (w1 scratch, `../xv6iris-weak-w1/MachCSL/SpikeP.lean`
831 l., `PROGRESS-W11F.md` §6): `interp_land :537` goes through over the minimal interpretation, consumes no client
resource, `readBytes_land :448` (landing changes no read at views ≤ the landed top); the per-address + epoch buffer
goes through too (`interp_landE :556`; FIFO is a special case, `landOk_landOkE :418`) → [OWN.113] CONFIRMED;
`memModel_issue :645` keeps the pushed postcondition; `wp_s_sw_core :718`; `read_casesP :784`/`read_cases_floorP :820`;
the land arm is SILENT and absorbed ONCE in the lifting lemma (`wpHart_lift_obsP`, per-event rules unchanged); churn
census: 27 MachCSL files, ≈ 411 errors (≈ 250 mechanical; the epoch adds 0) + 319 position comparisons in MachCSL /
87 lines in 16 Xv6 files whose meaning shifts; MachCSL churn measured 6–10k (the first design said 8.5–15k).**
**P-W1 MERGED at the tip (`zsqxzoqp`: `Weak/SbCand.lean` 751 l., `SbCandLit.lean` 136, `LitmusSBAcqP` §5; `Weak.lean:804-805`)
with finding F-P-W1-1 (§1 row 5: an `.aq` AMO may overtake only pending entries of the CURRENT fence epoch that do not
touch its bytes — rule 4; adopted for P-M1's AMO rule).**  Size ≈ **13.3–24.0k (MachCSL 7.8–14.1k serial, Weak 5.5–9.9k),
98–222 h**, confidence M on the machine (P0(c) passed) and M on progress; **P-M1 is launchable now.**  **[rev 56]: P-M1..P-M4 and P-W2..P-W4 LANDED; Σ P remaining 13.5–26.8k (the switch branch 5.3–9.8k + the queue 2.7–6.3k + P-W5/P-W6 2.4–4.3k + the load-side residue P-W3r 3.1–6.4k), ≈ 100–245 h; the branch is RUNNING (§5, §7).**

**FINDING F-P1 (→ Q-P-R1, RULED [OWN.111]: P re-confirmed).**  The UART 3-hart chain that the K spike (§3, §6) and the
K0 census (§3) present as the xv6-reachable instance of Litmus 2 is **excluded by the header's own trusted I/O item**:
`ioResidue` arm (R1) (`Weak/GraphFabResidue.lean:12-18`, "RAM access po-before an I/O event" ⇒ `gmoLt`, part of
`ioResidueGmo`, a premise of T-alloc-RVWMO) orders hart 2's `sleep_prepare` release store `w‴` (RAM, `0x80000cfa`)
before its THR store `X` (`LIo`, `0x80000988`) in gmo; the chain needs `X < … < r3 <fr w‴`, a gmo cycle.  The 2-hart
UART variant (census §3 end) dies the same way.  **Machine-checked in P0(b)** (`Weak/LitmusSBAcqP.lean` §2):
`SBAcqP.uCat`/`uCatT` (the chain is RVWMO-consistent), `SBAcqP.uIoNo` (in EVERY gmo with its rf and fabric order
`ioResidueGmo` fails), `SBAcqP.uNoR1Ok` (the witness satisfies (R2), (R2′), (R3) — (R1) is exactly the excluding arm).
The census's "`w‴ <gmo X` is not required" is true of RVWMO + PMAs and false under (R1), which is STRONGER than
RVWMO + PMAs and already trusted.  Consequences: (i) the only F44-1 shape known to be in the quantifier is **Litmus 1**
(2 harts, nested locks); (ii) δ1′ (acquire floor = rf-source position; `SBAcq.l1MemberSrc`) covers every 2-hart shape
and, modulo the census's completeness, every xv6 shape — but RELIES on (R1) for the UART chain, while **P replays it
without (R1)** (§4, [R45.7]); (iii) P is the only route robust to shapes the census did not find.  The owner
re-confirmed P with this in hand ([OWN.111], 2026-10-19 ~01:4x).

**FINDING F-R45-1 (R45 §2.1; → Q-P-WFENCE-REF, RULED [OWN.112] (a)).**  The design's first progress argument (§3.4,
now SUPERSEDED) rested on P-WFENCE, "every foreign-readable plain store is WCrel or `lk->cpu`".  P0(a)
(`notes/W10-P0a-wfence.md` §4.3) found it FALSE — the four `ip->ref` stores `iget+0x58`, `idup+0x1c`, `iput+0x22`,
`iput+0x8a` are foreign-readable (`fs.c:300,325`: `ip->ref < 1` read with no lock at `ilock+0xe`, `iunlock+0x1c`) and
not WCrel (seven fences in the image, `LockFacts.fenceCensus :137`, none in `acquire`) — and gave two 2-hart
executions that deadlock the landing gate through the FIFO edge.  R45 then showed the deadlock is **not a FIFO
problem**: a 3-hart RVWMO-consistent execution (§3.4 below) deadlocks the gate with NO buffer-order edge at all — two
unsynchronized reads reordered on one hart (`ilock+0xe`'s `lw` satisfied after the program-later `holding+0x0` `lw`) —
so a per-address buffer would not remove it, and the reader-side exception is required under EVERY buffer shape.  With
it `noStuckP` holds faithfully by a finite per-head table (§3.4).  The owner chose the exception ([OWN.112] (a)).

## 1. Spec first — what RVWMO / riscv.cat / Sail require of the buffer

Terms.  *Issue*: the store's instruction executes (the hart-local effect: forwarding becomes possible).  *Land*: the
store enters the global store order (gets its timestamp; foreign harts can see it).  *FIFO*: a hart's pending stores
land in issue order (the FALLBACK instance).  *Per-address + fence-epoch* ("P-set", THE instance [OWN.113]): a pending
store may land when no OWN pending store issued before it overlaps it (rule 1) and none of an earlier fence epoch
remains (rule 4).  *Fence epoch*: the count of `pw ∧ sw` fences the hart has executed (`rw,w`, `w,w`, `rw,rw`, `w,rw`,
`tso`; the draining ones empty the buffer anyway).  *Drain*: a step that cannot proceed until the hart's buffer (or the
entries overlapping an address) is empty.  *Forward*: an own load returns the hart's own latest pending byte.

| # | riscv.cat / spec rule | what the buffer does | mark |
|---|---|---|---|
| 1 | `[M];po-loc;[W]` (CoWW, CoRW) | same-hart same-address plain W→W: land in issue order (`landOk`'s overlap clause); R→W: the write lands later than any view the read used; an exclusive/AMO/SC write (lands at the top at once) to a buffered byte: the exclusive READ first drains the overlapping entries (`sbOverlaps` guard).  **[R45 A7]** riscv.cat orders the own store before the AMO's WRITE, not before its READ (forwarding) — the drain at the read is a machine STRENGTHENING, harmless for the quantifier (same value, same rf/co; a different mo witness); the progress measure of a drain-blocked exclusive read is the pair's WRITE position (§3.4 H5) | FAITHFUL (quantifier); machine STRONGER at the exclusive read, harmless |
| 2–3 | `[R];po-loc-no-w;[R]`, `rsw`/`fri` coherence | per-byte coherence floors as today (`HRead.coh`); an own pending store intervening resets the floor at ISSUE (forwarding then returns the own byte, co-later than anything landed) | FAITHFUL |
| 4 | FENCE pred/succ | pw∧sr (`rw,rw` `rw,r` `w,rw` `w,r` `tso`, and `iorw,iorw` — Sail drops the i/o bits, FIOM = 0, so it is `rw,rw` for RAM and orders nothing against MMIO in the graph, SAIL-GAP-1): DRAIN, then today's `fencePost` (`TsoMem.lean:491`; floor past `ownPub`, now the landed own last store).  pw∧sw only (`rw,w`, `w,w`): NO drain — it BUMPS the hart's fence epoch, so every entry issued before it lands before every entry issued after it; R→W is free in a single order (as today, `TsoMem.lean` header).  pr∧sr (`r,r`, `r,rw`): floor := rv, no drain.  `r,w`: no-op | FAITHFUL for the drain fences; **[OWN.113] the per-address + epoch buffer is FAITHFUL as a MACHINE too** (2+2W and unfenced-writer MP are machine behaviours, exactly RVWMO's store side); the FIFO fallback is STRONGER as a machine (it orders ALL same-hart plain stores), FAITHFUL for the GF quantifier iff `noStuckP`'s (E1) case is discharged (§3.4) |
| 5 | `[AQ];po;[M]` | an `.aq` exclusive read: floor := top (landing top) as today; it does NOT drain, and the pair's write lands at once, overtaking the buffer (the F44-1 freedom) — **F-P-W1-1 (P-W1, adopted): it may overtake ONLY the pending entries of the CURRENT fence epoch that do not touch its bytes.**  The first design let it overtake the WHOLE buffer, which violates rule 4: a `fence rw,w` orders every earlier store before every later WRITE, and the AMO's write is one (critical-section store → `release` → the next acquire's `amoswap` must not overtake the critical-section store).  So the exclusive write carries the SAME epoch guard as a landing (own entries of earlier epochs must be landed first — a blocked arm like the same-address drain); `SbCand` already has it | FAITHFUL (owner [OWN.110]; corrected by F-P-W1-1) |
| 6 | `[M];po;[RL]` | an `.rl` exclusive access drains everything first (xv6 has no `.rl`: `LockFacts.amoCensus :74`) | FAITHFUL |
| 7 | `[RCsc];po;[RCsc]` | an `.aq` AMO after an `.aq` AMO: both writes land at once in order (same epoch) — free; an `.aq.rl` drains by rule 6 | FAITHFUL |
| 8 | LR/SC pairs, atomicity | LR = exclusive read (drains overlapping entries, reservation as today); SC lands at once; a LANDING is blocked while another hart reserves the footprint (`othersReserve`, moved from issue to landing) | FAITHFUL |
| 9–13 | addr/data/ctrl deps, pipeline | reader-side; the machine tracks no dependencies (more permissive than RVWMO as today); a dependent store lands after the read it depends on anyway | unchanged (machine more permissive; theorem unaffected) |
| load value | visible = gmo-before ∨ po-before; co-max | own pending entries are po-before and will land after everything landed, so they are co-max among the visible: FORWARD per byte; mixed sizes: byte `j` from the hart's latest pending entry covering it, else the history at the load's view (`readFwd`) | FAITHFUL (cat is per byte; N10 mixed-size caveat unchanged) |
| Zifencei | stores ALREADY VISIBLE to the hart before `fence.i` visible to its later fetches; no data ordering | `fence.i` DRAINS, then raises `itv := max itv (max tv (max rv pub))` (**[OWN.143] F1**, 2026-10-21: `rv` joined, `fencePost true true`; the ifetch agent never forwards).  The drain is a data effect Zifencei does not have (EX-FENCEI-1, `notes/rvwmo-machine-examples.md`); removing it needs the fetch to forward the hart's own pre-`fence.i` stores AND falsifies the registered T4 export as stated (F-143-1, `PROGRESS-W11F.md` §13.1), so it is kept pending a ruling.  **O-P-W1-a (P-W1):** the pf label `LFence false×4` names BOTH `fence.i` and the `sfence.vma` marker; `SbCand` does not drain on it (faithful to RVWMO, which has no fetch events), MachCSL drains at `fence.i`, and xv6 executes `fence.i` (`userret`) → the buffered twin W4-P (P-W6) needs a distinct fetch marker to relate the two (P-W6 item, +0.1–0.3k) | `itv` past `rv`: FAITHFUL (F1); the drain: machine STRONGER (fewer runs; was mis-marked FAITHFUL until 2026-10-21, `notes/rvwmo-spec-audit.md` Q-AUDIT-2) |
| `sfence.vma` | orders prior PTE stores before later implicit walker reads of the same hart | no-op as today (Q7): the walker's reads are the hart's plain reads and FORWARD from the buffer — cat's load value already forces a po-earlier own store to be read | FAITHFUL w.r.t. cat ONLY under the modelling choice "walker reads are explicit loads" (riscv.cat has no implicit accesses); STRONGER than the privileged spec's prose, which lets implicit reads be early/stale until `sfence.vma` (audit §2 row 4, §4 item 3; unchanged from today) |
| A/D write-back (Svadu) | implicit exclusive pair | the walker's A/D update is an exclusive pair: same-address drain, write lands at once (`pteDiscAt` unchanged) | FAITHFUL |
| I/O (PMAs) | MMIO ordered against RAM only by `fence` i/o bits, deps, rule 5 | MMIO accesses are NOT buffered (`devRead`/`devWrite` at the event, as today) and do NOT drain the RAM buffer: a buffered RAM store may land after a later MMIO store | **WEAKER than RVWMO + PMAs on fences with i/o bits**: Sail drops the i/o fence bits at decode (`InstsEnd.lean:18299-18314`, D48; `notes/sail-gaps.md` SAIL-GAP-1), so `fence iorw,iorw` / `fence w,o` order nothing against MMIO in the model (dependency edges, appendix (c1), and rule 5 are kept).  The compensating text is the trusted (R1), STRONGER than the spec (QEMU-TCG: MMIO acts as a one-way fence), kept until the capstone [OWN.142].  P's claim not to use (R1) (§4, §6 A4) must still be checked on the fenced NOTIFY shape (EX-IO-1 in `notes/rvwmo-machine-examples.md`; audit §2 row 7, §4 item 2) |
| DMA | silent in RVWMO | the disk reads/writes at the landing top as today; xv6's `fence iorw,iorw` before every notify drains, so descriptors/data are landed when the device looks — true in the MACHINE (the drain); in the GRAPH the descriptor stores are ordered before NOTIFY only by the trusted (R1), since Sail drops the fence's i/o bits (SAIL-GAP-1; EX-IO-1; audit §4 item 10) | unchanged (device-model items of §B(11) stay) |
| interrupts, traps, `sret`, `wfi`, context switch | not fences | no drain (the kernel's hand-offs go through releases) | FAITHFUL |
| power loss | — | pending stores are lost (single era [R2.2]; the disk's durable image holds only DMA'd data) | FAITHFUL |
| narrow δ1 (stale silent AMO, `MState.silentOk` `Lang.lean:446`) | — | **RETIRED inside P-M1 ([OWN.114] (c), [R45.5])**: under P a failed acquire reads the LANDED top (the release has not landed ⇒ 1), so the stale arm is never used by the replay; the δ1 pieces are DELETED in the same edit and strict audit as the buffer (`xstale :123`, `afterExclStale :173`, `storeSilent :187`, `fenceWv :217`, `MState.fence`'s `wv` line `:236`, `staleFree :439`, `silentOk :446`, `staleBlocked :454`, the `not_silentOk_*`/`staleFree_*` lemmas `:458-480`, `blockedStep`'s stale arm, `WpLock`'s stale acquire outcome, `MachOfPf`'s and Vtest's stale cases; `MState.wv` goes with them).  Keeping it dead with `σ.sb cpu = []` would cost +0.3–0.8k of extra cases in every stale lemma P-M1..M8 re-proves (R45 A10), not 0.1k | FAITHFUL ((a)/(b) would keep one extra harmless behaviour) |

**The LOAD side ([R46.1]; [OWN.121] → [OWN.123]).**  Terms.  *gmo*: riscv.cat's global memory order.  *Stale view*: a load
returning a write older than the latest landed one at its byte, allowed when no co-later write is visible at the hart's
view.  *Logical load buffer*: an operational device letting a later-in-po load be satisfied before an earlier one.  *LB
(load buffering)*: a later-in-po STORE becoming visible before an earlier load is satisfied (needs promises).  *Head*: a
row's next GF event in the walk; *blocked head*: one the value gate rejects (`SbOrd.srcGate :75`/`valGate :81`: the
member's top ≠ GF's value); *late landing*: the walk's `land` gate (`landG :105`) holding a store back while a GF reader
of the byte's member-latest write is unrealized.

| # | riscv.cat / RVWMO rule on loads | MachCSL-P as a MACHINE (`Lang.lean:1708-1711`, `TsoMem.lean:356-358`, `:491`) | the replay (member `SbCand`, gate `SbOrd.enbL :88`) | mark |
|---|---|---|---|---|
| L1 | load value axiom: a read returns a write gmo-before or po-before it, not overwritten before it in gmo (per byte) | `readFwd`: own pending byte, else the history at a view `tvn ∈ [tv, top]` (`ltop` after the switch) | reads the member's TOP (forwarded or latest landed); the GF source is the top by the gate | FAITHFUL (quantifier); the member's gmo differs from GF's where GF had the read earlier |
| L2 | rules 2–3 (`[R];po-loc-no-w;[R]`, rsw/fri): two same-byte reads return co-nondecreasing writes unless an own write intervenes | per-byte `coh` floors raised by FOREIGN sources only, reset at own stores (`afterLoad`/`resetCoh`) | reads in po at the top: automatic | FAITHFUL |
| L3 | rule 4 with `pr` (`fence r,r`/`r,rw`/`rw,*`): earlier loads before later accesses | floor := `rv` (the read watermark, `fencePost :491`) | po-respecting: automatic | FAITHFUL |
| L4 | rule 5: `.aq` read before everything po-later | the exclusive read sets `rv`/floor := top; xv6's only `.aq` is `acquire+0x1c`'s AMO read half | AMO reads `rmwLatest` (landed top, atomicity); H1 `aqOrd` | FAITHFUL (machine STRONGER only at the exclusive read's same-address drain, row 1 above) |
| L5 | R→R to DIFFERENT bytes, no fence/dep: UNORDERED (no rule) | stale views (`tv` is NOT raised by a load) | **late landing**: the overwriting landing waits for the earlier-in-po reader; the replay never uses stale views (member loads at `tvn = ltop`) | FAITHFUL; stuck only if the earlier read is a blocked head — the per-site table (§3.4) |
| L6 | R→W to different bytes, no dep/fence: UNORDERED (LB allowed) | NOT modelled (loads execute in program order, no promises) | the store is issued after the read is realized; harmless unless the store is WAITED ON while the read is blocked (F-HH2-1) | machine STRONGER; FAITHFUL for the quantifier: no reachable LB shape of this binary (census leaf [R46.s1]: every census read → branch/fence before any foreign-readable store; only own-frame stores at `holding+0x12`/`mycpu` and `ismapped+0x10`'s return path precede the branch) |
| L7 | rules 9–13 (addr/data/ctrl deps, `[M];addr;[M];po;[W]`) | none tracked (more permissive) | the member respects po, hence every dep; the emission's `dsCtl`/`dsLd` edges are used only in the progress hops (`wrHopOfCtl`, `diskWrHop`) | unchanged (theorem unaffected) |
| L8 | mixed size / misalignment: per byte | per byte (`readFwd`, `textAt4S`) | per byte | FAITHFUL (N10 caveat unchanged) |
| L9 | LR/SC reads | LR = exclusive read, drains overlapping own entries | no LR/SC in the image (`LockFacts.amoCensus`) | n/a (machine STRONGER, harmless) |
| L10 | loads vs I/O: ordered only by fence i/o bits (Sail drops them, D48), deps, rule 5, PMAs | MMIO loads at the event | fabric order (R3); **(R2″) [OWN.116]** I/O → later RAM READ (`GraphFabResidue.ioResidue :123-138`) | STRONGER (trusted platform text, removable with (R1): A4; REVISIT list item 2) |
| L11 | loads of DMA-written RAM: silent in RVWMO | device writes land at once | never pending; an unissued device write ⇒ device-row progress (`diskWrHop`, (R2′), `diskFabPo`) | device-model text (named `diskFabPo`), FAITHFUL to the model |
| L12 | a read whose GF source is a store its hart has NOT YET REACHED (cross-hart R→W freedom) | n/a | `blkLoad :942`'s unissued-source edge → the source row's head, through `waitedOn :170` (the source is a write) | FAITHFUL; the dual of F-HH2-1 (§3.4) |

**[R46.s2]** `HRead`'s stale-view freedom — a plain load raises `rv` and the foreign-sourced `coh` floors, never the hart
view `tv` (`HRead.afterLoad` `TsoMem.lean:356-358`) — IS RVWMO's rules 2–3 in view form; it stays in the machine for the Xv6
proofs and is left UNUSED by the replay (member loads at the landed top).  Nothing here changes what riscv.cat/RVWMO/Sail
say.

The buffer changes NOTHING about what RVWMO/riscv.cat/Sail say; with [OWN.113] the machine's store side IS RVWMO's.
The machine stays STRONGER than RVWMO only where it already was (the exclusive read's drain, row 1) **and on the load side
by forbidding load→store (LB) reordering — harmless for the quantifier: no RVWMO-consistent GF of this binary has an LB
shape (census leaf [R46.s1], row L6)**; no dependency tracking is the opposite direction.  No load buffer, in the twin or
in MachCSL ([OWN.123]).

## 2. The MachCSL change (serial lane; the registered machine edited, statements unchanged, strict audits — the
[OWN.105] precedent)

### 2.1 State (`MachCSL/Lang.lean:97-131` `MState`, `TsoMem.lean`)

Design choice (the load-bearing one — "issue stamps as identities, landing positions as the order"):

* `log : List Agent` becomes the ISSUE log (`top` = issue top; a store's history entry `⟨top+1, h, v⟩` is pushed at
  ISSUE, exactly `MState.store`'s `mem`/`log`/`pcAt` updates `Lang.lean:205-208` — the entry's `t` is its ISSUE
  stamp, a stable identity; `pcAt` stays keyed by it, so `relProvAt` is untouched);
* NEW `lp : Nat → Option Nat` (landing position of stamp `t`; `none` = pending) and `ltop : Nat` (landing top);
  NEW `sb : CPU → List (Nat × Nat)` (the hart's pending stamps with their fence EPOCH, oldest first; invariant:
  exactly the own stamps with `lp = none`) and `sbEp : CPU → Nat` (the current epoch, bumped by every `pw ∧ sw`
  fence) — **[OWN.113]**; the FIFO fallback ignores the epoch (P0(c) item 5 keeps `landOk` a PARAMETER with both
  instances type-checking);
* histories are kept in CO order: landed entries by `lp` descending, PENDING entries on top of them.  The issue
  step inserts the new entry at the top of each footprint byte's history; **an exclusive or DMA write (which lands at
  once) is inserted BELOW the pending prefix (`Hist.insLanded`/`landBytes` in the spike), not `pushed`** — so an AMO
  postcondition on a byte holding a foreign pending entry changes shape (the lock word with a pending release: P-M6;
  P0(c) risk (3)).  For a byte that already holds ANOTHER
  hart's pending entry the issue step chooses the relative position nondeterministically (the machine must be
  total); for xv6 this never happens (`pendOne` §2.4; R45 A13 checked the racy classes: `ip->ref` writers are under
  `itable.lock`, `lk->cpu` holder-only, `started` hart 0, PTEs owner), and every store WP rule knows it from its
  precondition.  **[rev 58] THIS BULLET WAS NOT IMPLEMENTED (F-PW6-1, P-W6 spike; A7 §2): the registered machine pushes every issued
  entry on TOP of the byte's history (`FlatMem.writeBytes` `TsoMem.lean:188-194`), `histOkP :900` keeps pending entries co-ordered by
  descending stamp ACROSS authors (`coAbove :890`), and `landFootOk` (`Lang.lean:453-456`) needs every entry below landed — so two
  harts' plain stores to one byte LAND IN ISSUE ORDER (`SbRealP.landBlockedForeign :1145`), which RVWMO does not require and the twin
  does not do (`wit1Run :1176`).  STRONGER than RVWMO — the plan's STRENGTHENING LEDGER row 5.  The vocabulary exists (`MState.pendOneAt`
  `Lang.lean:1214`, one consumer; `ctxLandedAt :1229`, no consumer outside `Lang.lean`; `pendOneOfCtx` absent) but the rule and its
  coupling do not.  Ruled [OWN.149]: bridged NOW on the graph side — the walk input `IssueCo` (same-byte plain stores issue in co order)
  + the lock-hand-off census `SbBlocked.Hb` (plan N15, inside P-W6) — and REMOVED after the capstone by **R-PF′** (plan row A6): keep
  `issue` as is, let `MState.land` insert the entry BELOW the pending prefix with `Hist.insLanded` (`:818`, already used for AMO/DMA
  writes; `histOkP_insLanded :1397` proved), drop `landFootOk`'s "no pending below" clause; the WP burden (≈ 20–30 plain-store rules gain
  the `pendOne` side condition) is the same as this bullet's, the invariant work smaller.  (xv6 satisfies `pendOne`: every shared byte is
  written under a lock or by one designated hart, and the previous holder's stores are of an earlier fence epoch than its release.)**
* views `tv`, `itv`, `hr.rv`, `hr.coh` are LANDING positions (`wv` is deleted with δ1).  `HEnt.visible lp h tv e :=
  (lp e.t).any (· ≤ tv) || e.tid = h`; `Hist.read lp h tv H := (H.find? (visible lp h tv)).map v` — unchanged shape,
  one more argument (co order IS the list order, so the first visible entry is the co-maximal visible one);
  `Hist.top` = the first LANDED entry; `histOk` = descending `t` among the whole list is DROPPED, replaced by
  `histOkP`: pending prefix (all `lp = none`, descending `t`, one author) then landed suffix descending in `lp`,
  every landed `t` present in `llog` at its `lp`, and PER BYTE the same author's entries land in issue order (rule 1
  — this is what `landOk`'s overlap clause guarantees; under the FIFO fallback it is `lp` monotone in `t` per author);
* `ownPub h log` → `ownPubL`: the landing position of `h`'s last LANDED store (= its last store after a drain);
* `bootFacts`: `lp = fun _ => none`, `ltop = 0`, `sb = fun _ => []`, `sbEp = fun _ => 0` (`Lang.lean:398-403`,
  `bootWitness :414`).

### 2.2 Rules (`evStep` `Lang.lean:525-575`, `blockedStep :581-589`, `hartStep :692-697`)

```lean
-- issue (plain RAM store): no reservation check, no landing
| .memWrite n _ req, plain, ramBytes: σ' = σ.issue cpu req.pa n w            -- push ⟨top+1, cpu, w⟩ at each byte's
                                                                              -- top, log ++ [cpu], pcAt, sb ++ [(top+1, sbEp cpu)],
                                                                              -- hr.resetCoh (rule 2), tv untouched
-- land: a NEW arm of hartStep (the hart stutters one of its pending stores into the order)
| hartStep: … ∨ (landOk σ cpu t ∧ m' = m ∧ σ' = σ.land cpu t)
  -- [OWN.113] per-address + fence-epoch (THE instance):
  landOk σ cpu t := (t, ep) ∈ σ.sb cpu ∧ ep = oldest epoch in σ.sb cpu                      -- rule 4 (`landOkE`)
                    ∧ (∀ byte of t's footprint, t is the LOWEST pending entry of that byte's history)  -- rule 1 / co ⊆ landing
                    ∧ ¬ othersReserve σ.resv cpu (footprint of t)                            -- (own included: spike)
  -- the footprint clause (P0(c) risk (2)) covers own AND foreign pending entries on the byte — the first design's
  -- `landOk` lacked it; FIFO fallback: landOk σ cpu t := σ.sb cpu = (t, _) :: rest ∧ footprint ∧ ¬ othersReserve …
  -- (`landOk_landOkE`: a FIFO head landing IS an epoch landing)
  MState.land σ cpu t := { σ with lp := lp[t ↦ ltop+1], ltop := ltop+1, llog := llog ++ [t], sb := (sb cpu).erase t }
                                                                              -- mem, log, pcAt UNCHANGED; obs = [] (SILENT)
-- plain load: forward, then the history at a view in [tv, ltop]
| plain read: ∃ tvn w, tv ≤ tvn ∧ tvn ≤ ltop ∧ cohOk ∧ σ.readFwd cpu tvn pa n w ∧ σ' = σ.afterLoad cpu pa n tvn
  readFwd: byte j := the hart's latest pending entry covering pa+j if any (sbByte), else Hist.read lp (hartAgent cpu) tvn
  (afterLoad's loadSrcs stamps a forwarded byte 0 — own-sourced, as today)
-- exclusive read (LR / AMO read half / walker A/D read): same-address drain first
| excl read: ¬ sbOverlaps (σ.sb cpu) pa n ∧ ¬ othersReserve … ∧ topBytes at the landed top      -- no stale arm [OWN.114]
  blockedStep gains: akExcl ∧ sbOverlaps (σ.sb cpu) pa n ∧ σ' = σ   (self-loop until the landings happen)
-- exclusive write (AMO write / SC / A/D write-back): lands at once, INSERTED BELOW the pending prefix (`insLanded`, lp := ltop+1)
| excl write: no own pending entry of an EARLIER epoch remains (F-P-W1-1, rule 4), else blocked (Löb arm)
| excl write with rl (akRel, NEW classifier): additionally σ.sb cpu = [] (rule 6), else blocked
-- fences
| .barrier b: (fenceDrains b ∨ fenceIfetch b) → σ.sb cpu = [] (else blocked, NEW blockedStep arm); σ' = σ.fence cpu b with pub := ownPubL
|             (fencePw b ∧ fenceSw b) → sbEp := sbEp + 1                                            -- the epoch bump [OWN.113]
-- δ1: DELETED (silentOk / staleBlocked arms and the xstale field go) [OWN.114]
-- devices: dmaView/storeDma read/append at the LANDING top (ltop); unchanged otherwise
```

Why the landing is a hart arm and not a thread: a separate `Expr.sb` thread would change `powerFork`, the pool
relation of W4 (thread indices `MachOfPf.lean` header), `riscvPowerAdequacy`'s `Reducible` conclusion and Vtest's
executor; the hart arm touches `hartStep`, the two lifting lemmas `wpHart_lift_obs`/`wpHart_lift` (`Wp.lean:190,308`)
and the four `wpLoop_restart*` (`:2775-2879`, a Löb self-loop exactly like the K multi-tick arm, `W10-K-spike.md`
§2 R-K1) — provided landing is GHOST-INVISIBLE (§2.3).  Reducibility: the arm is enabled whenever the buffer holds a
landable entry; a drain-blocked fence self-loops (`blockedStep`), so `Reducible` is unchanged.
**P0(c) VERDICT (w1 `PROGRESS-W11F.md` §6, 2026-10-19; PASSED):** (1) the land arm must be SILENT — `primStep` emits
`hartObsM cpu m` keyed on the head event, so a stuttering landing at a `cur_privilege` write would emit a spurious
uEnter/uExit; the hart arm is split (obs = [] on the land arm), `ObsTrace.primStep_obsWf` adapted.  (2) A land arm at
ANY `m` is NOT absorbed by the plain lifting shape (the callback is consumed at the pre-step state; a later credit
would need `InvGS_gen .hasLC`, but MachCSL is generic in `hlc`) — RESOLVED by **`wpHart_lift_obsP` with `interp_land`
as a hypothesis**: land disabled → callback first (as today); land enabled → the step is reducible by the land arm,
the callback is POSTPONED into `wp_lift_step_fupd`'s `£1 ={∅}=∗ ▷` window (its ▷ merged with the step's), no credit;
a landing step → `hland` + the SAME wp by Löb.  **The land arm lives ONLY in the step relation and is handled ONCE in
the lifting lemma; `wpHart_lift`, `swp_event_*`, `wpLoop_restart*` and the per-event rules compile UNCHANGED**
(census A′).  Recommended P-M shape (coordinator): land arm only in the step relation, handled in the lifting lemma;
guard = oldest epoch + footprint; the FULL `interp_land` early in P-M2 as the acceptance gate.

### 2.3 The state interpretation (`Resources.lean:2101` `eraInterp`, `:2193` `powerInterp`, `Adequacy.lean`)

The one principle: **a landing changes no resource any client can hold.**  Clients hold `histBytes`/`wordCell`
frags of the MERGED history (`σ.mem` as defined in §2.1: pending entries on top with their issue stamps) — landing
does not touch `σ.mem`, so these frags are unchanged.  What landing changes is `lp`/`ltop`/`sb`, which live in the
interpretation only:

* `lpAuth lp` (a monotone map: `none → some p` once) with PERSISTENT frags `landedAt t p` (`t ⤳ p`), minted by the
  interpretation at the landing and handed out by the rules that LEARN them (below); `sbAuth cpu l` owned by the
  interpretation alone (no client frag: the hart's knowledge of its own buffer is the list of own entries with no
  `landedAt` — a derived notion `pendingOf cpu H`); **NEW the fence-epoch token** `epochAt cpu k` ([OWN.113]): a
  persistent frag "every own entry issued before the hart's `k`-th `pw ∧ sw` fence lands before every own entry
  issued after it" (`landedBeforeOfEpoch`), minted by `wp_s_fence_rw_w` (`WpLock.lean:36`, today "unchanged");
* the view resources `hartViewsAt` (`:995`) keep their shape (landing positions);
* NEW invariant clauses: `histOkP` (co-ordered histories, per-byte issue order per author), `pendOne` (§2.4), and
  **`ctxLanded`**: for every certified context token (f2-ctx, `Ctx.lean`/`CtxBox.lean`: per-author vector bound
  `Vb`, release stamp `t_rel`, author `A`): whenever `lp t_rel = some p`, every entry of author `X` with stamp
  `≤ Vb X` is landed at `< p`.  It holds because (i) A's own entries `≤ Vb A ≤ t_rel` land before `t_rel` — **[R45.4]
  under the epoch buffer this is rule 4 through the release fence** (`release+0x16` `fence rw,w` adjacent to the
  store at `+0x1a`, `LockFacts.relAdj :113`; `main+0xac` before `started`'s store `main+0xb0`): every own entry
  issued before the fence has an earlier epoch than `t_rel`, so `landOk` lands it first (`landedBeforeOfEpoch`);
  under the FIFO fallback it is immediate from `sbAuth` — either way the RELEASE RULE must STATE it (P-M6); and (ii)
  a foreign author's entries `≤ Vb X` were LANDED when A acquired them (A's acquire floor is a landing position above
  them), and A's `t_rel` lands above any position that was the top at A's issue;
* **`pendOneOfCtx`** ([R45.4], R45 A5): the hop conversion EXPORTS "no foreign PENDING entry on the bytes I just
  acquired" — the previous holder's stores to the protected bytes precede its release fence, so they are landed when
  the acquirer's AMO reads the landed release; a corollary of `ctxLanded`, delivered by `memModel_chainHop` (P-M5);
* **`interp_land`** (the central lemma): `machInterp σ ⊢ |==> machInterp (σ.land cpu t)` — the ghost update of
  `lpAuth`/`sbAuth`, `histOkP`/`pendOne`/`ctxLanded` preserved, `mmOk`/`rsvOk` (`Adequacy.lean:485,501`) preserved,
  the chain conjunct (`:1495`), the kpt conjunct (`:1649`), the reserved-region conjunct (`:1832`), the user-epoch
  conjunct (`:2096`) preserved — each of these is stated over `σ.mem` and positions; they must be restated with
  `lp` where they order (`entAsOf`/`wordAsOf`/`memGrow`/`memAbove` in `ChainDefs.lean` — 126 comparison sites —,
  `KptInv` 25, `Lock` 22, `UEpoch*` 17, `WordHist` 10, `Reserved` 7) and are then INVARIANT under landing by
  monotonicity of `lp`.  **P0(c) verdict on ghost-invisibility: HOLDS for the minimal interpretation (heap untouched,
  every read at every view ≤ `ltop` unchanged — `readBytes_land` —, authority grows only).  In the FULL interpretation
  the conjuncts that read the LANDED top (`Hist.top`) are landing-sensitive and are P-M2's named work: `mmOk`'s
  reservation clause (protected by `landOk`'s no-reservation guard), **`curWordAt`/`uSlotNow` in `uepModelAt` (the
  user-epoch conjunct) must be restated over the MERGED history's head** (the walker is the own hart and forwards) or
  proven stable (risk (4)), `dmaView` (step-time only); `ctxLanded` is landing-sensitive by design.**

Adequacy (`riscvPowerAdequacy` `Adequacy.lean:270`) is generic over `primStep` through the interpretation: it needs
only `interp_land` and the new blocked arms' "state unchanged" facts; `powerInterp_mmOk`/`rsvOk`/`accessDisc`
(`AccessDiscipline.lean:1362`) keep their statements.

### 2.4 The WP rules: what stays, what changes

**Plain stores** (`wp_s_sw/sd/sb/sh` `WpSmodeRules.lean:353-713`, `WpSmodeFrame12b`, `WpStoreOrd`, `WpStoreFree*`,
`WpSmodeMint`, `WpSmodeAuRules`, `WpSmodeProc`; 901 uses in 219 `Xv6/` files): the POSTCONDITION keeps today's shape
`histBytes pa n dqs (pushed Hs (top+1) cpu w)` — the pushed entry carries the ISSUE stamp `top+1`, which is what
today's `t` is.  **[rev 58] Addition (i) is NOT in the registered machine (F-PW6-1; `memModel_issueQ/QLA` take no `pendOneAt` — A7 §2's implementation row);
it returns as R-PF′ after the capstone (plan row A6), with the count corrected to ≈ 20–30 plain-store rules ([B6.2]: `WpSmodeRules` 9,
`WpLock` 9 + `WpLockInit` 4, `WpStoreOrd` 3, `WpSmodeAuRules` 3, `WpSmodeMint` 2, `WpStoreFree`/`WpSmodeProc`/`WpSmodeFrame12b`/`WpStore` 1
each; MMIO excluded), not "≈ 12".**  Two additions: (i) a side condition `pendOne`: the footprint holds no FOREIGN pending entry — read
off the frag (`∀ e ∈ Hs j, e.tid ≠ cpu → landed e`), and discharged in the rule's own proof from the resource the
rule already demands (full fraction, or the custody class whose only plain writer is the holder/owner: lock words,
`started`, `au`/`auT` words, PTE slots, mint/free pages) — the Xv6 call sites do not see it, and for the custody
classes the FACT is delivered by the hop (`pendOneOfCtx`, §2.3 [R45.4]); (ii) no reservation check at issue (one
premise fewer).  `pcAt`/`relProvAt` (`wp_s_sw_auT_pc` `WpStoreOrd.lean:375`) unchanged.
**Key lemma shapes** (new, in `WpAtomic.lean`/`Resources.lean`, replacing `memModel_store_*`'s plain half):
```lean
memModel_issue : mmOkP σ → pendOneAt σ pa n cpu → ramBytes pa n →
  machInterp σ ∗ histBytes pa n dqs Hs ⊢ |==> machInterp (σ.issue cpu pa n w) ∗ histBytes pa n dqs (pushed Hs (σ.top+1) cpu w)
interp_land  : machInterp σ ⊢ |==> machInterp (σ.land cpu t)                                   -- §2.3
landedAt_of_drain : after `fence` with pw∧sr (or fence.i / rl): ∀ t, authored cpu t → t ≤ σ.top → ∃ p ≤ tv', landedAt t p
landedBeforeOfEpoch : epochAt cpu k → authored cpu t → authored cpu t' → issuedBeforeFence t k → issuedAfterFence t' k →
  landedAt t' p' → ∃ p < p', landedAt t p                                                       -- [OWN.113] the fence token
```
**Plain loads** (`memModel_read_*`, `exists_read_top`, `readsAre`, `read_cases`/`heads_eq` in `WordHist.lean`): the
side condition "`e.t ≤ tv` ⇒ the head is read" becomes `visibleAt e tv := landedAt e.t p ∧ p ≤ tv ∨ e.tid = cpu`.
Xv6 proofs rarely state `e.t ≤ tv` themselves (11 `Xv6/` files compare `.t` against positions: `AccessDiscipline`,
`DiskAcc`, `DiskInvDefs`, `IcachePinwObl`, `IcacheInvRef`, `KptTextIdent`, `KptMapIdent`, `StartedInv`,
`TextPristine`, `UEpochClose`, `UEpochDeposit`); they get visibility from the CONTEXT layer: `kctxL`/`ownCtx` with a
bound, converted at hops by `memModel_chainHop` (`Lock.lean` header of `isLock :1636`).  Under P the hop conversion
yields `visibleAt` (and `pendOneOfCtx`) from `ctxLanded` + the acquire's floor; the bound stays an ISSUE-stamp vector
bound (`Vb`, which [OWN.38]'s per-author design already is).  So: the context/hop lemmas change (`Ctx`/`KCtx`/`CtxBox`/
`CtxX`), the load rules' statements change their visibility side condition, most Xv6 call sites do not.
**Locks** (`WpLock.lean` 3.9k, `Lock.lean` 2k, `LockPayIff`, `LockBornHook`, `Reserved.lkFold :85`, `lockWinAt :140`):
the lock word's `WordHist 4` is read as a co-ordered list — with pending-on-top it already IS (the holder's pending
release sits above every foreign AMO write that lands meanwhile, and stays above when it lands: §2.1), so `lkFold`'s
alternation `A R A R …` is the LIST alternation as today; what changes is `lockWinAt`/`lockHistOk`'s "as of position"
reading (`lp`), and the release rule (`wp_s_sw_zero_release_*` `:2235-3649`) which must (i) mint the `ctxLanded`
certificate for its payload's vector bound — **[R45.4] stating "my stores issued before the release fence land before
this store"**: under the epoch buffer from the `epochAt` token `wp_s_fence_rw_w` minted one instruction earlier
(`relAdj`), discharged once at `release+0x16`/`+0x1a` and once at `main+0xac`/`+0xb0`; under the FIFO fallback from
`sbAuth` —, (ii) not assume the release is visible at issue — the lock protocol's "released" state is entered
at ISSUE (ghost) while the word's landed value is still 1; the ACQUIRE rule (`wp_s_amoswap_lock*` `:1217-1760`) reads
the landed top, so a foreign acquire can fail against a pending release — that is a new, legitimate failed-spin case
of the acquire's loop (the same `bnez` arm; no new state), and a successful acquire reads a LANDED release, from
whose `landedAt` the floor and the hop follow; the δ1 stale outcome of the acquire rule is DELETED ([OWN.114]).
`lkCpu_read_not_mine :283` (the `lk->cpu` value clause) is unchanged in shape: the holder's pending `lk->cpu = me`
store is on top of the merged history and is a hart's own entry.  **Shape change (P0(c) risk (3)):** a foreign
acquire's AMO write on a lock word whose holder's release is still pending is inserted BELOW that pending entry, so
the AMO/lock-word postconditions (`wp_s_amoswap_lock*`) state `insLanded`, not `pushed`, on such a byte — P-M6's
new case beside the failed spin.  The AMO's write also carries F-P-W1-1's epoch guard (own earlier-epoch entries
landed first — for the holder's own `release` → next `acquire` this is the critical-section stores, discharged from
`landedBeforeOfEpoch` after the release fence).
**Fences** (`wp_s_fence_r_rw*`, `_iorw_iorw*`, `_rw_w` `WpLock.lean:36`): `rw,w` MINTS the epoch token ([OWN.113];
no drain, no blocked arm); the draining ones gain the `landedAt_of_drain` postcondition and a blocked arm (Löb, like
`wpLoop_restartB`).
**AMOs / walker pairs** (`WpAtomic`, `UMemAmo*`, `UkfWalk`): the exclusive read's same-address drain precondition is
discharged from the hart's own knowledge of its buffer (`pendingOf`) — for the lock word the holder never has a pending
store to it except its own release (which it issues last), for PTE slots the walker is the same hart as the writer
only inside `sfence`-bracketed code; the rules state the drain as a Löb-blocked arm.
**Devices / DMA** (`WpDev*`, `WpDevDma` leases `dmaWriteLease :46`, `dmaReadPin :75`): MMIO rules unchanged; the DMA
lease rules need "the leased bytes are landed" — true after the driver's `fence iorw,iorw` (`landedAt_of_drain`), a
new premise auto-discharged at xv6's call sites (the W-DMA0 pattern [OWN.34]).
**Boot / Vtest**: `bootFacts`, `BootRun`, `vtest-lean/Vtest/XState.lean` (mirror of `MState`: `xstale` mirror
removed, `lp`/`ltop`/`sb`/`sbEp` added) and `HartExec.lean` (executor policy: land immediately after issue — keeps every
existing Vtest trace).

### 2.5 The export (`Xv6/AccessDiscipline.lean:1106-1108`, eleven conjuncts, `Xv6.xv6DiscAdequacy_closed`)

The conjunct LIST is unchanged (append-only kept; eleven at the tip: `… ∧ relProvAt ∧ dynLockWinZAt ∧ ksFrameAt`).
Sub-definitions that ORDER by position read `lp` instead of `t` (`chainOkAt :327`'s load-side clause at view `tvn`;
`lockWordDiscAt`/`lkCpuReadAt` windows; `dynLockWinZAt :934`'s `(p, t]` and `entAsOf … p`; `ksFrameAt :1027`'s
`s < e.t`; `uptDiscAt`/`utextDiscAt` "after `itv`"); `relProvAt` (keyed by issue stamp) and `kptMapsExp`/`cpuStaticAt`
are untouched.  Weak consumes the export through `rmem` (`Weak/PfStepTsoMem.lean`), which W4-P restates (§3.6);
`RvwmoXv6Adequacy.lean` picks conjuncts by position — unchanged.  As with X1's `custAt` carve, the export's
sub-definitions move while `tcb/expected.json`'s module set moves once if a new MachCSL module is added (keep the new
definitions inside `Lang.lean`/`TsoMem.lean` to avoid it).

### 2.6 What Xv6 proofs see of a buffered store — the answer to the brief's question

Yes, "own buffered store visible as owned memory to its hart" is exactly the merged-history ghost: the hart's own
pending entry is an ordinary history entry it authored (visible to it at every view, co-max for it), so every own
read-back, every `tailOk`/`histBytes` manipulation and every transfer of `a ↦ H` into an invariant keeps today's
text.  The price is paid in three places only: visibility of FOREIGN entries (landing certificates instead of
`t ≤ tv`), the hop conversion (`ctxLanded` + `pendOneOfCtx`), and the lock word's two readings.  The rules do NOT stay
unchanged in their proofs (every memModel lemma is re-proved), but their STATEMENTS at the Xv6 interface do, except
the load rules' visibility side condition, the drain fences' extra postcondition, and the AMO postcondition on a byte
with a foreign pending entry (`insLanded`).  P0(c) confirmed it: `wp_s_sw`'s statement does not break (only
`Wp.swp_sail_mem_write_plain`'s body is re-proved), and the per-event rules see no land conjunct.

## 3. The Weak side

### 3.1 The twin candidate `SbCand` (replaces `SilCand` as the realization's candidate; primed twin, registered
`mstep`/M1/M2 untouched [OWN.97][OWN.100]) — **P-W1 DONE, MERGED at the tip** (`zsqxzoqp`; `Weak/SbCand.lean` 751 l.,
`Weak/SbCandLit.lean` 136 l., `Weak/LitmusSBAcqP.lean` §5 (752 → 886 l.); `Weak.lean:804-805`)

`Mstate` (`Weak/WeakAxiomatic.lean:107`) + the pending entries per agent (`SbEnt`, with their epoch).  **The landing
policy is a PARAMETER `SbPol`** (`SbCand.lean:44-110`: four laws `inRange`, `oldest`, `sameAddr` (rule 1), `fenced`
(rule 4); instances **`SbPol.epoch` — PRIMARY per [OWN.113]**, `SbPol.fifo` — the fallback; **`SbPol.leEpoch`: epoch is
the WEAKEST lawful policy = exactly RVWMO's store order**, so a member under FIFO is a member under epoch).  Steps:
`MStepLoad` with per-byte forwarding (a forwarded byte's label timestamp is left to P-W2); `issue` for `LStore` (push,
no log append; `storePostRun`'s position-dependent parts deferred); `land` (ADMIN step, no label: `msLog ++ [m]` for
any policy-landable pending entry, the deferred view updates at the landing position `|log|+1`); `MStepFence` with
drain preconditions mirroring §2.2 (and the epoch bump); `MStepRmw` reads `rmwLatest` at the landed log — a failed
acquire against a pending release reads 1 at the top: no silent arm — **and may overtake only current-epoch pending
entries not touching its bytes (F-P-W1-1)**; `MStepIo` unchanged; no LR/SC in the label set.  Embedding: every
registered run is an `SbCand` run with each store landed right after its issue (`SbCand.execWfOfOld`).
Machine-checked: `SbCandLit.l1MemberSb` (Litmus 1 is an `SbCand` run with GF's labels verbatim under EVERY lawful
policy, instantiated at `SbPol.epoch` and `SbPol.fifo`, `SbCandLit.lean:73-78`); `LitmusSBAcqP` §5: `l4Cat` (the
F-R45-1 GF, THREE rows, cat-consistent), `l4NoMemberP` (NO gate-respecting member without the [OWN.112] exemption,
policy-independent — the deadlock is not a buffer-order artefact), `l4MemberX` (a member once `e_B` reads the landed
top).  Spec: FAITHFUL (the candidate-level twin of §2).

### 3.2 The walk and THE GATE ([OWN.106]: built step by step; no order premise, no acyclicity assumed) — with the
two-site exception ([OWN.112], [R45.1])

State: `SbWalk.St` = `SilWalk.St` (`Weak/SilWalk.lean:27-36`) with `c : SbCand.CandS`, program states `pst`, fabric
`dv`; the dependency shadow `sh` (`SilDep`, needed only to bound the silent write) is DROPPED.  Enabledness of row
`x` at its next GF event `e`, and of a landing, at walk state `S` (member-latest `latestW S b`, realized set):
```lean
/-- the two value-insensitive racy reads (`fs.c:300,325` `ip->ref < 1`; census 6m §3.3; P0(a) §5) — LANDED
    `Weak/SbReplay.lean:66` (as a `Prop`) -/
def ipRefPc (pc : Int) : Prop := pc = sym KernelSyms.«ilock» 0xe ∨ pc = sym KernelSyms.«iunlock» 0x1c
/-- **REVISIT [OWN.124]** — the THIRD exempt pc ([rev 56], F-HH2-1 (a), [R46.2]): `holding+0x12` = `0x80000c04`
    `ld a5,16(a0)` (`lk->cpu`, read UNLOCKED inside `acquire`'s `holding(lk)`; `SilSiteTab.kSites` row 2, `.PResidue`).
    Exempt like `ip->ref`: the member reads the top of `[L+16, L+24)` (own forwarded `sd zero` or the latest landed
    value), GF reads its source; both are `≠ cpuAddr x` for a non-holder `x`, so `holding` returns 0 on both sides.
    The owner flagged this exemption to be looked at again; alternative (b) — a custody-aware `waitedOn` + `FrameQuiet`'s
    third clause + a NEW per-load MachCSL footprint record + P-W6 lookahead glue, 1.1–2.2k — is on file (§3.4). -/
def holdCpuPc (pc : Int) : Prop := pc = sym KernelSyms.«holding» 0x12
def exemptPc (pc : Int) : Prop := ipRefPc pc ∨ holdCpuPc pc
def exemptRd (GF : Gfexec) (e : Geid) : Prop := gisR e ∧ exemptPc (pcOf GF e)      -- pc from the emission state (T)

inductive SbOrd.enb (GF D fab) (S) (cnt) : Item → Prop
  | fab   : nextIsFabric GF S cnt x → enb (.ev x)                              -- fabric members in fabric order (R43)
  | rd    : gisR e → ¬ exemptRd GF e → (∀ b, srcOf GF e b = some w → landedOrOwn S x w b) → enb (.ev x)
            -- every GF source LANDED in the member (or the row's own pending store: forwarding)
  | rdX   : exemptRd GF e → enb (.ev x)     -- [OWN.112]/[OWN.124] no source gate; the member reads the landed top / own pending
            -- (LANDED for the two `ip->ref` pcs as `SbReplay.rdXArm :705`; the third pc is row P-W3r-a, w3)
  | wr    : gisW e → (∀ b, coPred GF e b = some w0 → latestW S b = some w0 ∧ readersRealized GF S w0 b) → enb (.ev x)
            -- an AMO / exclusive write: its GF co-predecessor is member-latest and all its GF readers are realized
            -- (for an AMO this includes the rf gate: the source IS the co-predecessor; `srcLatest` of R44 §2 + the
            -- K-spike's "reverse divergence" fr-gate, item 5, made uniform)
  | plain : plainStore e ∨ lbInert e ∨ gisIo e → enb (.ev x)                   -- issue is always enabled
  | land  : landablePol pol (σ.sb x) w → (∀ b, coPred GF w b = some w0 → latestW S b = some w0 ∧ readersRealized GF S w0 b) →
            noResv … → enb (.land x w)

/-- value agreement: exact everywhere except at the three exempt pcs — at the two `ip->ref` pcs both words are in
    [1, 2^31) (LANDED `SbReplay.valEqX :744`, `irefOkL :740`); at `holding+0x12` NEITHER word is the reading hart's own
    `cpuAddr` ([R46.2]; `x` = the row's hart) -/
def SbAgree.valEqX (GF) (S) : Prop :=
  ∀ r ∈ realized S, (¬ exemptRd GF r → memberBytes S r = gfBytes GF r) ∧
                     (ipRefRd GF r → irefOk (memberWord S r) ∧ irefOk (gfWord GF r)) ∧
                     (holdCpuRd GF r → memberWord S r ≠ cpuAddr (row r) ∧ gfWord GF r ≠ cpuAddr (row r))
/-- the `ip->ref` value facts.  [rev 56] F-P-W2-1: `irefGe1` is NOT GF-provable (process migration moves the reader's
    own `ref++` to another hart) → [OWN.117] M12-a/M12-b: the GF side `IrefGF` (`SbReplay.lean:750`) from a MachCSL record
    on `iput`'s closing 0-store, the member side `IrefTop` from a racy-load ghost record "`ip->ref` seen ≥ 1" — both via
    P-W6; NAMED until the MCSL queue items Q5/Q6 land -/
theorem irefGe1 (GF) (B : row) (x : write of ref) : ownInc GF B ≤co x → x ≤co srcOf GF e_B → irefOk (val x)  -- SUPERSEDED by IrefGF/IrefTop
/-- the `lk->cpu` value facts ([R46.2]/[R46.3]).  GF side: `SbHeadHop2.HoldZero :479` — every `holding+0x12` read inside
    `acquire(L)` by row `x` has GF value `≠ cpuAddr x` (x's po-last own write to `[L+16)` is its last release's `sd zero`
    — no recursive acquire, the MachCSL proof's precondition —, every co-later write is another hart u's `sd a0,16(s1)`
    with `a0 = mycpu() = cpuAddr u`, `u ≠ x`, or a 0; CoWR puts GF's source co-at-or-after x's own write).  Member side:
    the export twin `lkCpuReadAtP` (`Xv6/AccessDiscipline.lean:1467`: a non-holder reading `lk->cpu` at ANY view from an
    initial `v0 ≠ cpuAddr c` never obtains `cpuAddr c`) applied at `tvn = top` via P-W6's state map, "x is not the
    holder" read off x's own realized lock-word history.  No new MachCSL record. -/
theorem holdNotMine (GF) (S) (r : holdCpuRd) : memberWord S r ≠ cpuAddr (row r) ∧ gfWord GF r ≠ cpuAddr (row r)
/-- datum: the registered lockstep datum with TAINT at the two sites — LANDED as static rules already:
    `SilSiteTaint.ruIlock`/`ruIunlock :647-650` (the loaded `a5` feeds only the `blez` at `ilock+0x10` / `iunlock+0x1e`)
    and the value rule `SilSite.ruleOfIrefPos :207` (both values ≥ 1 ⇒ same arm); P-W2 re-hosts them on `SbCand` -/
theorem ipRefTailDies : ∀ pc, ipRefPc pc → loadTailDies pc {a5}          -- LANDED `SbReplay.ipRefTaint :75` / `ipRefRule :90`
/-- [rev 56] the third taint arm ([R46.2]): from `holding+0x12` (`a5` tainted) through `mv s1,a5` (`0x80000c06`: `s1`
    tainted too) and `jal mycpu` (`0x80000c08`) — `mycpu` `0x8000195c`–`0x8000197a` writes `sp`/`ra`/`s0`/`a5`/`a0` only, never
    a callee-saved register other than its own saved/restored `s0`, and its frame stores `sd ra,8(sp)`/`sd s0,0(sp)` carry
    UNTAINTED registers (`decide +kernel`) — to `sub a0,s1,a0` (`holding+0x1a`) and `seqz a0,a0` (`holding+0x1e`), where
    BOTH sides give `a0 = 0` by `holdNotMine`: the taint dies by the value lemma, as `ilock`'s dies at `blez`; `s1` is
    then reloaded from the frame (`ld s1`) in `holding`'s epilogue.  Needs the taint walker to cross ONE call (if the
    landed walker stops at `jal`, +0.1–0.3k) and the Sail meaning of the 14-instruction path (O-P-W2-a's open item,
    larger here) — inside row P-W3r-a. -/
theorem holdCpuTailDies : loadTailDies (sym KernelSyms.«holding» 0x12) {a5, s1}
```
**Value agreement by construction (`SbAgree.valEqX`; LANDED P-W2 `Weak/SbReplay.lean:744` for the two `ip->ref` pcs,
`agreeX`/`agreeW3OfX`/`agreeW4OfX` in `SbAgree.lean`; the third pc is row P-W3r-a).**  Invariant: at every walk state, for
every byte, the member's landed co order is a prefix of GF's co at that byte (`PInv.pfx`, PROVED P-W2/P-W3), and every
realized read other than the three exempt pcs returned its GF source's bytes.  At `holding+0x12` the member's word is
the top of `[L+16, L+24)` (0 after a release/`initlock`, or another hart's landed `cpuAddr u`), GF's is its source
(possibly a pending `cpuAddr z`); `holdNotMine` gives both `≠ cpuAddr x` ([R46.2]).  Proof per arm: `rd` — the source is member-latest (landed by the gate and nothing co-later has
landed: a co-later write's landing/AMO waits for this reader by `wr`/`land`); own pending source — forwarding returns
it (GF's load value says the read returns the own po-earlier store or a co-later write; a co-later write cannot have
landed before an own pending store, so it is the own store); `wr`/`land` — the co prefix extends by GF's next write;
`rdX` — the member's landed writes to `ref` are a GF-co PREFIX, the reader's own `ref++` (`iget+0x58`/`idup+0x1c`,
program-before `e`) is landed or forwarded, and every landed write co-after it is in `irefGe1`'s interval, so the top
the member reads is ≥ 1 (`racyValOk :314` of the export says the same at the realized MachCSL state for an unchained
foreign entry; the GF lemma serves both sides).  Hence the member's labels are GF's up to re-indexing (`lblReidxW`
with EQUAL values except at the three exempt pcs), the datum is the registered lockstep datum (`CertZ9.lockstepStep` /
`CertZ13.hartStepOfSite` with `csync`) with TAINT at the three pcs (`CertZ13.relT`, `CertZ11.loadTail`), `relT`
lockstep everywhere, and `agreeW4`'s four clauses (`CertZ24.lean:72-87`) hold with `nf = True` except at the three pcs —
including FULL lock co (`lockCoSP` for free: member co = GF co per byte; `SilOrd2`'s windowed reconstruction §1–2
becomes unnecessary).  **[rev 56] P-W2 findings:** F-P-W2-3 — `agreeW4` at the REAL `L` is false, consumers use
`agreeW3OfX`/`agreeX`; F-P-W2-2 — the member is not `gwrowGmo`, so P-W4's kill glue goes through RVWMO ppo (`SbKill`,
LANDED).  [OWN.108] is SUPERSEDED ([R45.8]): a pinned load is gated on "source landed" and replayed at
the member's TOP, which equals the GF value because the overwriting landing is held back; no stale replay, and the
per-site view/value datum of row 6m is vacuous except for the three exempt pcs.
**Spec marks of the exception.**  (a) FAITHFUL (the GF is admitted; only the member's value at a value-insensitive
read differs, and the published statement speaks of GF's values through the kill, not the member's) — RULED
[OWN.112]; (b) a NAMED premise excluding these GFs would be WEAKER and false-ish (they are reachable xv6 behaviours);
(c) a kernel change (`ref` read under `itable.lock`) is out of scope [OWN.4].  Cost: `rdX` + `valEqX` + `irefGe1` +
re-hosting the two-site taint ≈ +0.4–0.8k on P-W2/P-W3 over the first design (of which `irefGe1` 0.2–0.4k was already
in row 6m's budget; the taint rules exist) — LANDED in P-W2 (2,763 l. incl. the walk/agreement layer).
**Spec marks of the THIRD exemption (`holding+0x12`, F-HH2-1; RULED [OWN.124] (a) + REVISIT).**  (a) exempt the read:
FAITHFUL (the GF is admitted; the member may read 0 or another hart's pointer where GF read z's pending pointer; both
`≠ cpuAddr x`, so `holding` returns 0 on both sides and the published statement speaks of GF's values) — an xv6 expert
reads "at three unlocked sanity reads (`ip->ref` ×2, `holding`'s `lk->cpu` compare) the replay may see a different value
than the graph did; both values give the same branch"; cost 0.6–1.2k Weak / 5–10 h (`rdX`/`valEqX` glue 0.2–0.4k, the
call-crossing taint arm + its Sail meaning 0.3–0.6k, the member-side fact from `lkCpuReadAtP` 0.1–0.2k), NO new MachCSL
record; risk M (the pattern exists, the call-crossing taint is new).  (b) a custody-aware measure: replace `waitedOn`'s
write arm `gisW G m` (`SbOrd.lean:171`) by "a write to a BUSY byte" (`busy w a := (∃ pending entry writing a) ∨ (∃ AMO head
writing a) ∨ (∃ load head whose GF source byte is a)`; `tgtW :446` gains the busy hypothesis at both call sites
`blkLand`/`blkAmo`; `tgtEv`/`HeadOrdRd`/`descent` unchanged); then `mycpu`'s frame stores are waited on only if some OTHER
row's head load reads x's live frame, and `FrameQuiet` (`SbHeadHop2.lean:492`) must gain exactly that clause — about
another hart's UNREALIZED next load's footprint, which no current export gives (`ksFrameAtP :1539` constrains landed
ENTRIES; `chainOkAtP` constrains observed entries AFTER the load) → a NEW per-load MachCSL footprint record ("a load's
footprint avoids other harts' live frames", from the static regions + X1's page-provenance record) + a one-step-lookahead
glue in P-W6; FAITHFUL and general; 0.3–0.7k Weak + 0.5–1.0k MachCSL (serial lane) + 0.3–0.5k glue = 1.1–2.2k / 9–21 h —
**KEPT ON FILE as the owner-flagged alternative**.  (c) name `noStuckP`: WEAKER, rejected by the [OWN.100] standard.
Shared by (a) and (b): `HoldZero` (§3.4, row P-W3r-b).

### 3.3 Why the two shapes are lockstep (walk-throughs; §4 has the full tables)

Litmus 1: both releases ISSUE (pending), both acquires of `e`/`c` land at once, each hart's spin read of the other's
lock is enabled (source = the other hart's acquire write, member-latest because the release is pending) and reads 1,
each failed `amoswap` is enabled (its co-predecessor is that acquire write; its readers — the spin reads — are
realized) and appends 1, and the releases LAND only after the last GF reader of their co-predecessors (the last
stale spin iteration) is realized, right before the acquire that GF has reading them.  Cross-spin ([OWN.100],
CertZ23/CertZ35's block): the same with the roles symmetric.  No skip, no silent step, no stale view.  Machine-checked:
`SBAcqP.l1MemberP` (P0(b) §3, the FIFO core) and `SbCandLit.l1MemberSb` (P-W1: an `SbCand` member under every lawful
policy).  F-P-W1-1 does not disturb it: each release store is issued AFTER its own `fence rw,w`, so it is in the same
epoch as the hart's next acquire and may be overtaken.

### 3.4 Progress — `noStuckP`, RESTATED per R45 §2.4 ([R45.1][R45.2]; replaces the P-WFENCE argument, kept below as
the record)

**Items** at a walk state: `head x` (row `x`'s next GF event `e_x`) and `land(x, w)` (a pending store of row `x`).
In a step-by-step walk ([OWN.106]) these are the ONLY items; a GF reader `r` of a co-predecessor is not an item — the
edge lands on the HEAD `e ≤po r` of `r`'s row, and `gmo(e) < gmo(w)` is NOT given (load-load reordering: `r <gmo e`
is legal) — which is exactly where the first design's (E3)/(E4) were loose (R45 A2).
**Edges** (A waits for B): (E5) `head x` → `land s`: `e_x` a gated read with a FOREIGN pending source `s`;
(E6) `head x` → `land w` (own): `e_x` a draining fence / `.rl` / an exclusive read overlapping `w` / an exclusive
WRITE with `w` of an earlier epoch (F-P-W1-1; rule 4 makes it gmo-backward like the fence case);
(E2w) `head x` → `land w0`: `e_x` an exclusive write whose co-predecessor `w0` is pending;
(E3w) `head x` → `head y`: `e_x` an exclusive write with an unrealized GF reader `r` of its co-predecessor on row `y`;
(Efab) `head x` → `head y`: `e_x` a fabric member not next in fabric order, row `y` holds the next one;
(E1) `land w` → `land w′`: `w′` overlapping `w` or of an earlier epoch (THE instance, [OWN.113]) / FIFO-before `w`
(the fallback); (E2) `land w` → `land w0`: foreign co-predecessor pending; (E3) `land w` → `head y`: unrealized GF
reader of the co-predecessor on row `y`.
**Measure** µ: `µ(land w) = gmo(w)`; `µ(head x) = gmo(e_x)` for a memory or I/O event (I/O events are `gmem`);
for a FENCE head, the gmo position of the row's first memory event after the fence (a fence head with none has
only (E6) edges and is on no cycle); for a drain-blocked exclusive-READ head, the position of the pair's WRITE (A7).
**Claim: every edge strictly decreases µ, hence the waits-for graph is acyclic and some item is enabled.**
(E5) rf ⊆ gmo; (E6) rule 4 / rule 6 / rule 1 (to the pair's write); (E2w),(E2) co ⊆ gmo; (E1) rule 1 / rule 4 under
the epoch buffer — **no census input** (under the FIFO fallback: the WCrel census `notes/W10-P0a-wfence.md` §3, five
strict WCrel sites, as a `decide +kernel` leaf, + the `lk->cpu` reader-side lemma of census §4.1); (Efab) (R3) of
`ioResidueGmo` — the one trusted arm the proof uses; (E3w),(E3): `r <fr w` gives `gmo(r) < gmo(w)` (`SBAcq.frLt`), and
the HEAD `e_y ≤po r` needs **`gmo(e_y) ≤ gmo(r)`** — the per-head table:

| head kind | why `e_y ≤gmo` every later read `r` of its row | status |
|---|---|---|
| H1 `.aq` AMO (every kernel AMO: `acquire+0x1c`, G1 `kernelAmoAq`) | rule 5 | static, planned (6l G1, now inside P-W3) |
| H2 draining fence | rule 4 (`pw ∧ sr`) | by definition of µ |
| H3 gated plain read with a pending or unissued foreign source = a BLOCKED HEAD, which is a RACY census site (`SilSiteTab.kSites :71-96`: 18 kernel pcs; + 8 device `DRead` nodes) | **[rev 56] replaced by the PER-SITE TABLE below ([R46.6]; `SbHeadHop`/`SbHeadHop2` §HEADHOP2)** — the rev-55 cell is the record: it said "`holding+0x0/+0x12` → no read between" (FALSE on `holding+0x0`'s nonzero arm and at `holding+0x12`: F-P-W3-1, F-HH2-1) and "`virtio_disk_intr`: never blocked" (FALSE on vdi+0x36's fall-through and vdi+0x82's back edge, which legitimately WAIT for the device row's idx write — covered by `fenceNextHop`) | `HeadOrdRd :251` NAMED as the interface; (a1) static hops + (A2) windows PROVED; per-site inputs = rows P-W3r-* |
| H4 fabric member | (R3) + **(R2″)** ([OWN.116]: an I/O access po-before a later RAM read is gmo-before it — F-P-W3-2 found (R3) alone never orders I/O before a later RAM read) | trusted arms (REVISIT list item 2: removed with (R1) in A4) |
| H5 drain-blocked exclusive read (walker A/D pair on an own pending PTE) | rule 1 to the pair's write; readers of the PTE's co-pred are custody-chained | PROVED (every AMO `.aq`: a drain-blocked exclusive read is H1) |

**The per-site table ([R46.6] = §HEADHOP2 re-derived by R46 §3; the complete LOAD-SIDE obligation of route P).**  Method:
a head is blocked iff the member's top ≠ GF's value at some byte (`valGate`), i.e. GF's source is a pending or unissued
FOREIGN store (own stores forward; landed sources make the top GF's value because the co-successor's landing waits).  A
chained read's source is landed when the read becomes the head (the hop AMO is realized only when its source, the
release, is member-latest = landed; the release's `fence rw,w` puts every earlier store of the releaser in an earlier
epoch — `landOk`'s oldest-epoch clause — so they landed first; `started` likewise through `main+0xac`; device writes land
at once).  For each blocked site the walk needs (A1) every later WAITED-ON write gmo-after the head and (A2) every later
waited-on pure read past an ordering point (`headOrdRdOf`), or "never blocked", or an exemption.  **(T)** = the
realization's label↔pc transport (P-W6), listed ONCE here and named nowhere else.

| site (image pc) | blocked possible? | load→store before the branch? | (A1) | (A2) | named input / verdict |
|---|---|---|---|---|---|
| `holding+0x0` from `acquire+0x12` (`0x80000bf2` `lw a5,0(a0)`) | yes: zero arm (GF 0 = a pending release, top 1), nonzero arm (GF 1 = an unissued swap, top 0) | no: `bnez` next (`0x80000bf4`) | rule 11 via `dsCtl` (`wrHopOfCtl` + `ctlOfPsites`) | zero arm: next event is the `.aq` AMO (`aqNextA2`); nonzero arm: the window to the AMO holds `holding+0x12` (quiet by **`LkCpuQuiet`**: no pending `lk->cpu` store while the landed byte is 0) and own-frame reloads (quiet by **`FrameQuiet`**), then `bnez a0` → AMO or panic (excluded by **`HoldZero`**) | PROVED mod (T), `LkCpuQuiet`, `FrameQuiet`, `HoldZero` — no escape |
| `holding+0x0` from `release+0xc`/`sched+0x14` (caller holds) | no: top = 1 = GF (the holder's AMO landed, spinners write 1, nobody writes 0) | — | — | — | **`HeldPin`** (realized-prefix lock fact) — no escape |
| **`holding+0x12`** (`0x80000c04` `ld a5,16(a0)`) from `acquire` | **yes**: the holder z's `sd a0,16(s1)` (`acquire+0x28`) pending, GF reads it, top is 0 or an older pointer | **YES**: `mv s1,a5; jal mycpu` → `mycpu+0x2/+0x4` `sd ra`/`sd s0` before `seqz`/`bnez` | **FALSE** for the frame stores (no dep, no fence; pin `PResidue`) | window = `mycpu`'s and `holding`'s frame reloads (quiet) → `bnez a0` → AMO | **F-HH2-1 → EXEMPT [OWN.124] (a), REVISIT**; needs `HoldZero` (GF side) + `lkCpuReadAtP` (member side) |
| `holding+0x12` from `release`/`sched` | no: the holder's own `sd a0,16` forwards or is landed (own source) | — | — | — | no escape |
| `main+0x16` (`started`) | yes (GF 1, hart 0's `main+0xb0` pending) | no: `fence r,rw` next | rule 4 (`main16FenceNext`) | rule 4 | PROVED mod (T) |
| `ilock+0xe`, `iunlock+0x1c` (`ip->ref`) | exempt (`rdX`, [OWN.112]) | no: `blez` next | — | — | exempt; value by `IrefTop`/`IrefGF` ([OWN.117] M12-a/b, Q5/Q6) |
| PTE ×9 (`walk+0x32` … `uvmclear+0x10`) | no: custody — the table's writers are the owning process's hart (or the walker on it); hand-offs through `p->lock`; the reaper reads a ZOMBIE's table after `wait`'s acquire | 7 × ALU only to the branch (`ptePctrlAlu`); `ismapped+0x10` returns the value (its caller branches after `ld ra`/`ld s0` reloads — loads, no stores); `uvmclear+0x10` data-dep into its `sd` (rule 10) | ctrl / data | NOT static — must be never blocked | **PTE custody** (Q-6M-PTE (a)) ⇒ `SrcLanded` ⇒ passes the gate — no escape |
| `virtio_disk_intr+0x36`/`+0x82` (`used->idx`) GF ≠ `used_idx` | yes (waits for the device row's idx write) | no: `beq`/`bne` next | `fenceNextHop` (vdi+0x3e `fence iorw,iorw`) | same | PROVED mod (T) |
| vdi+0x36 taken / vdi+0x82 fall-through (GF = `used_idx`) | no (device idx writes consecutive, `0 ≤ idx − used_idx ≤ NUM`, realized idx reads monotone ⇒ top = GF) | — | — | NOT static | **`VirtioIdx`** — no escape once discharged |
| vdi+0x4e (`ring[i].id`), vdi+0x5a (`info[id].status`) | no (the source is the device's completion write, `devStOrd`-before the idx the hart already read; landed) | no (`wrHopOfCtlR` through the `lbu`) | ctrl | NOT static | **`VirtioDesc`** — no escape |
| the 8 device `DRead` nodes | blocked while the driver's descriptor/avail stores are pending | n/a (device program) | `diskWrHop` PROVED (rule 13 `dsLd`) | NOT static (disk loads carry no deps) | **`DiskDesc`**: the source is a driver store po-before its REALIZED `fence iorw,iorw` ⇒ landed (**`drainLanded`**, a new `PInv` clause, 0.1–0.3k) — no escape |
| `forkret+0x18` (`lw first`, `0x800019c6`) | no: the writer (the first process, `0x800019d6`) is po-before its `fork`'s `release(&np->lock)`; the reader is resumed by a scheduler acquire of that lock | `beqz` next | — | — | chained (not a census site); `SpecForkret.lean:33` decides the branch by a token — consistent ([R46.s3]) |
| `procdump+0x70` (`lw p->state` unlocked, `0x80002482`) | would be (a foreign `p->state` store under `p->lock` pending) | `beqz` next; then `printk`'s `acquire(&pr.lock)` → `holding+0x0` on `pr.lock` before any ordering point — (A2) would FAIL | — | — | **DEAD TEXT**: no `jal <procdump>` in `Xv6/KernelImage.lean` (verified: the only references to `0x80002412` are its own entry and `KernelSyms.procdump`); its contract is stated unsatisfiable (`SpecProcdump.lean:40-45`); unreachable — no escape ([R46.s3]) |
| `panicked` / `pr.locking` readers | — | — | — | — | absent from this image (panic → `unreachable`); no escape ([R46.s3]) |
| user rows; `uservec`/`userret`/`swtch`; `kfree`'s fill; `log`/`bio`/`pipe*`; `wakeup`/`sleep`; `either_copyout` | no (chained: sources are own writes, the kernel's writes on the process's behalf, `fork`/`exec` by the parent → chained through `np->lock`, `kfree`'s fill through `kmem.lock`; trap/switch data written po-before the previous hart's `release(&p->lock)`) | — | — | — | no escape; rests on **`blockedIsCensus`** ([R46.4]) |

**Where the hunt's completeness rests** (all FAITHFUL program-layer facts, WEAKER only while named; the plan's
NAMED-INPUTS table [R46.s4] tracks them): (i) **`blockedIsCensus`** ([R46.4]; row P-W3r-c, 0.5–1.0k Weak, 4–8 h) — "a
plain-load head that is not a census site passes the value gate": own source ⇒ forwarded; chained source ⇒ the hop AMO
realized ⇒ release landed ⇒ epoch ⇒ landed (`srcGateOfLanded`/`valGateOfLanded`); device source ⇒ landed at issue; an
unissued foreign source is excluded by rules 4–5 against the row's realized acquire + the lock discipline of the GF rows
(`SbKill.l2ClaimP :507`, row 6n) — today hidden inside (T), now its own item; (ii) the per-site named inputs `HoldZero`,
`FrameQuiet`, `LkCpuQuiet`, `HeldPin`, `VirtioIdx`, `VirtioDesc`, `DiskDesc`, PTE custody, (T); (iii) the device model
(`diskFabPo`, `usedElemGateOk`).  None is a load-buffer question.

**`HoldZero` ([R46.3]; `SbHeadHop2.lean:479`; row P-W3r-b, 0.6–1.2k Weak, 4–10 h, NO MachCSL record).**  Statement: every
`holding+0x12` read inside `acquire(L)` by row x has GF value `≠ cpuAddr x`.  Why true: x's po-last own write to `[L+16)`
is its last release's `sd zero` (no recursive acquire — the MachCSL proof's precondition), every co-later write is another
hart u's `sd a0,16(s1)` with `a0 = mycpu() = cpuAddr u` (u ≠ x) or a 0, and the `cpus` pointers are distinct; CoWR puts
GF's source co-at-or-after x's own write.  Discharge path: REALIZED writes via `lockWordDiscAtP`/`lkCpuReadAtP` (P-W6);
PENDING or UNISSUED writer rows carry a GF label whose relation to `cpuAddr u` comes from the emission's register state
(`a0 = &cpus[tp]` at `acquire+0x28`, `mycpu+0x8` `mv a5,tp`) and the invariant `tp = row` at kernel pcs (boot `start`; after
user mode `uservec`'s reload of `kernel_hartid`, written by the same hart in `prepare_return` — the [OWN.77]/[OWN.87]
trapframe custody; `AxSpinT2a.mycpuRetHart :617` already gives `mycpu`'s value at `tp = hartId c`); `kfree`'s 1-fill and
recycled pages are excluded by restricting to LIVE published locks (`Lk`).  It also unblocks `holding+0x0`'s nonzero arm
(the panic exit).

**F-HH2-1, re-derived (R46 §3; the ONLY escape).**  At a reachable walk state: z won the swap on `L` (landed at issue),
z's `sd a0,16(s1)` is pending (no fence until z's release), x's `holding+0x0` realized (top 1 = GF 1), x's head `r12 =
holding+0x12` has GF source = z's pending store ⇒ top ≠ GF ⇒ blocked.  `mu (.hd x)` is the least gmo position of x's
unrealized waited-on events; `mycpu`'s `sd ra` is a write, hence waited on (`SbOrd.lean:171` `gisW`), and RVWMO lets it sit
gmo-before z's store (no rule orders `ld` → unrelated `sd`), so `mu (.hd x) ≤ gpos (sd ra) < gpos (z's store) = mu (.ld z _)`
and the (E5) edge does not descend.  Nothing is stuck (z's entry is landable: its co-predecessor's readers are
`holding+0x12` reads, all realized or not waited on); the MEASURE is too coarse.  **Are there more of its kind?**  A blocked
racy read followed by a store before the branch on its value: among the 18 only `holding+0x12` (frames) and
`ismapped+0x10` (never blocked; its path to the caller's branch has loads only); among the device reads none (device
programs store only after the fabric point).  The (A2) kind (a blocked racy read followed by a WAITED-ON read before an
ordering point): `holding+0x0`'s nonzero arm (quiet window — handled) and `procdump+0x70` (dead text).  **No new escape.**
The LB-freedom census leaf ([R46.s1], row P-W3r-d, 0.05–0.15k): for each of the 18 census pcs the instruction path to its
certified branch contains no store, except `holding+0x12` (own frames) and `ismapped+0x10` (return path) —
`holding0CtrlNext`, `main16FenceNext`, `vdiShape`, `ptePctrlAlu` exist; add `ilock+0xe`/`iunlock+0x1c` (`blez` next) and the
two exceptions as explicit statements.

Inputs of `noStuckP` ([rev 56]): `rvwmoCatConsistentT`, `ioResidueGmo` ((R3) and (R2″) only — (R1) unused), the image
(H1/H2 and the static hops by `decide +kernel`), `kernelAmoAq`, and the NAMED per-site inputs above (rows P-W3r-*; the
two buffer-state records `FrameQuiet`/`LkCpuQuiet` come from MachCSL Q7 after P-M8 via P-W6).  NO named premise in the
published statement once P-W3r lands (fallback: NAMED, WEAKER, 0).  Confidence M: the table is finite and mostly proved
mod (T).

**F-R45-1, the execution (R45 §2.1; MECHANIZED in P-W1: `LitmusSBAcqP` §5 `l4Cat`/`l4NoMemberP`/`l4MemberX`, three
rows, [R45.s2]).**  Byte `ref` =
`dp->ref`, lock `lk` = `dp->lock.lk` (the sleeplock's inner spinlock); harts A, B, C all hold a reference to `dp`:
* **A**: `iunlockput(dp)` → `releasesleep` → `release(&lk)`: `fence rw,w`; **`Y` = `sw zero` on `lk`**; then `iput(dp)`
  → `acquire(&itable.lock)` (`amoswap.w.aq`, no fence) → **`w` = `ref--`** (`iput+0x22`).
* **B**: `ilock(dp)`: **`e_B` = `ilock+0xe` reads `ref` = `w`**; `blez`; `acquiresleep(&dp->lock)` → `acquire(&lk)` →
  `push_off` → `holding(&lk)`: **`r_B` = `holding+0x0` reads `lk.locked` = 1** (A's acquire write in `releasesleep`,
  the co-predecessor of `Y`; stale).
* **C**: `ilock(dp)` → `acquiresleep` → `acquire(&lk)` → **`e_C` = `holding+0x0` reads `lk.locked` = 0 = `Y`**;
  `amoswap.aq` takes `lk`; … later `iunlock(dp)`: `holdingsleep` → `acquire(&lk)` … → **`r_C` = `iunlock+0x1c` reads
  `ref` = `w₀`**, the value BEFORE A's decrement.
gmo witness `r_B < Y < e_C < r_C < w < e_B`; load value satisfied; ppo on B: `e_B <po r_B` but nothing orders them —
`lw ref` → `blez` → `jal acquiresleep` → prologue stores → `jal acquire` → `push_off` (csr ops, per-cpu loads/stores) →
`holding`: `lw lk.locked`; different addresses, no fence, no `.aq`, no address dependency, and rule 11 orders
`ctrl;[W]` only (the per-cpu STORES are ordered after `e_B`; the LOAD `r_B` is not).  On C `e_C →ctrl amoswap.aq
→(rule 5) r_C`.  `rvwmoCatConsistent` holds.  **Under the gate without `rdX`:** head B = `e_B`, gated on `land w`;
head C = `e_C`, gated on `land Y`; `land Y` waits (E3) for `r_B`, behind `e_B`; `land w` waits (E3) for `r_C`, behind
`e_C`; A blocks at its next same-address drain — no item enabled, and NO buffer-order edge was used (under the epoch
buffer `land w` and `land Y` are independent; the cycle is identical).  Among the census's 18 kernel sites the pair
"racy read that may be a blocked head, program-before a stale-reading read of another byte" exists ONLY for `ip->ref`
(H3).  **With `rdX`** the walk is: `e_B` (reads `w₀`, ≥ 1, tainted until `blez`), `r_B`, `L(Y)`, `e_C`, …, `r_C`
(reads `w₀` = GF), `L(w)`, `e_B`'s taint already dead.

*[R45.1] SUPERSEDED — the first design's progress text (the record).*  It took the items as "the GF event behind
each item", called (E4) "a row's earlier unrealized event" an edge, and concluded that (E1) was the only
non-gmo-backward edge, to be discharged by **P-WFENCE** — (a) every foreign-readable plain store is WCrel
(`release+0x1a`, `started`), or (b) a `lk->cpu` store inside `acquire` whose FIFO-earlier stores are per-cpu words no
foreign row reads.  P0(a) refuted (a) (the `ip->ref` stores) and (b) (the FIFO-earlier set of `acquire+0x28` contains
the previous `release+0x1a`; census §4.1 gives the `lk->cpu` acyclicity from the READER side instead), and R45 showed
the (E1) census does not settle progress at all (F-R45-1).  Nothing of that text is load-bearing now.

### 3.5 Reuse / retire table

| piece | under P |
|---|---|
| `SilCand`/`SilCandLit`/`SilMember`/`SilDep`/`SilReplay`'s silent arm, `SilWalk2`, `SilRegZero`'s twin ghost, `SilClose` untrimmed kills, `SilOrd2`'s silent/pin arms | RETIRED as consumers (dead, keep green, headers "superseded by P"); `SbCand` is a new leaf beside them |
| `SilWalk` (state/snoc/okSnoc), `SilReplay.progOk` (program states), `SilAgree` (member/agreement shape), `SilPf*`/`SilEpf` (pf bridge) | REUSED, re-parametrized on `SbCand` (no `sil` column, no dep shadow, + pending lists) |
| `SilOrd2` §5–6 (the step-by-step gate `enb :743`, `prefW`/`prefG`, `walkPolG`, `recLogOfTr`, `cycleKillGZ`, `noStuckG :775`) | REUSED as the pattern; the gate's arms replaced by §3.2's (`silent`/`pin` arms gone, `rdX`/`land` arms added); §1–2 (windowed co reconstruction) UNNECESSARY (co agreement is total) — keep for the record |
| `SilSite` premises (`ordQ`/`silentQ`/`rmwQ`/`valQ`/`noPanicQ`/`custQ`/`drfQ`), `SilSiteStep`, the dynamic use of `SilSiteTaint` | RETIRED (values agree by construction, except the three exempt pcs — `ip->ref` ×2 [OWN.112], `holding+0x12` [OWN.124]); `SilSiteTab`/`SilSiteTaint` kept as the static census record AND re-hosted for the two-site taint (`ruIlock`/`ruIunlock`), `SilSite.ruleOfIrefPos` likewise; Q-6M-GFVAL, Q-6M-HOLD, Q-6M-ORDER moot; **Q-6M-PTE (a) NOT moot ([R45.3]): PTE custody at the realized prefix is a P-W3 input (H3/H5)** |
| `SilKillT.cycleKillCore :98` (twin-typed) → `cycleKillCZT` | REWRITTEN once for `SbCand` (`cycleKillCoreP`), same consumers (`CapFetchProv.t2linSupplyCZTtagged`) |
| `CapFetchProv`, `CapPcLog`, CertZ2–23 lockstep/transport, `CertZ9/13` datum, `LockFacts*`, `GraphFetchN2.csChainedT` | REUSED unchanged |
| CertZ24–34 (padded/skip/lag), the K-only rows 1′/6o/6p of R44; CertZ17's NF3/NF4 anchors (via `lockDiscCZ3`) | NOT needed (dead, green) |
| narrow δ1 inc 14–16b | DELETED inside P-M1 ([OWN.114]); its three changes stay in history |
| `CapF1.recRealizedH :50` (registered realization) | kept for M2; the member needs `recRealizedP` on the buffered twin W4 (§3.6) |

### 3.6 W4: two pieces

(a) **The registered `machRunOfPfRun` (`MachOfPf.lean:2958`) must be RE-PROVED** against the new `evStep` (serial,
right after the MachCSL change): a pf `LStore` row = MachCSL issue step + land step; the simulation invariant adds
"every buffer is empty at every related state", so drain preconditions are trivial, `rmem`'s `R-hist` becomes
"merged history with every entry landed, `lp t = some t`" (issue and landing coincide), `viewRel`/`TsoShadow`
positions unchanged.  **[R45.6] / A9 VERIFIED at the tip: `MachOfPf.simStep :2874-2887` concludes `(k ≠ .disk → m ≤ 1)`
— ONE pf step is at most ONE `hartStep` today**, so P-W5 needs either a two-step stutter (`m ≤ 2` on `LStore` rows;
`machRunOfPfRun` relates RUNS, so the bound is internal) or a fused `issueLand` arm (+0.1–0.3k) — P0(c) item (6)
picks.  0.8–1.5k, mechanical.  M1/M2 (`roots-weak.txt`) re-registered by re-proof, statements unchanged.
(b) **The buffered twin W4-P**: `SbCand` member runs (with pending lists) → MachCSL-P runs: `rmemP` = `rmem` +
`R-sb` (pending message lists with epochs ↔ `sb` stamps, with the merged histories' pending prefixes) + `R-lp` (pf log
position `k` ↔ `lp t = some (k+1)`); the land admin step ↔ the hart's land arm; loads at the member's top ↔ MachCSL
loads at `tvn = ltop` (always legal: `tv ≤ ltop`).  Its consumers: rows 6b (`segRealized`/`readAt` at the member) and
6j's E1 (the twin realization for `protReg` sourcing) — CapF6–CapF10's `readAt` parts re-derived at `recRealizedP`.
1.5–2.5k.

## 4. The two litmus shapes under P (lockstep tables)

Notation: `I(w)` issue, `L(w)` land, `R` member read value, `[gate]` why enabled.  Positions are landing positions.

**Litmus 1** (`SBAcq.l1`: hart 1: `A_b1; w′=rel b; A1=acq e; r1/F1 on d`; hart 2: `A_d2; w″=rel d; A2=acq c; r2/F2 on
b`; GF rf: `r1/F1 ← A_d2`, `r2/F2 ← A_b1`, later acquires `A_d1′ ← w″`, `A_b2′ ← w′`).

| step | item | gate | member effect |
|---|---|---|---|
| 1–2 | `A_b1`, `A_d2` | `wr`: co-pred = image/previous release, latest, no unrealized reader | land at 1, 2 |
| 3–4 | `I(w′)`, `I(w″)` | `plain` | pending on harts 1, 2 (histories: `b = [w′ᵖ, A_b1, …]`, `d = [w″ᵖ, A_d2, …]`) |
| 5–6 | `A1`, `A2` | `wr` on `e`/`c`: co-pred latest, readers realized | land at 3, 4 (no drain: w′, w″ stay pending) |
| 7 | `r1` (`holding+0x0` on `d`) | `rd`: source `A_d2` landed ∧ latest (w″ pending) | R = 1 = GF |
| 8 | `F1` (failed `amoswap.aq d`) | `wr`: co-pred `A_d2` latest; its readers (`r1`) realized | lands at 5, value 1 (= GF's RMW) |
| 9–10 | `r2`, `F2` on `b` | symmetric | R = 1; lands at 6 |
| 11… | hart 1's further spin iterations on `d` (GF reads `F1`'s 1) | `rd`: source `F1` latest | R = 1 |
| k | `L(w″)` | `land`: co-pred of `w″` at `d` = GF's last pre-release writer (`F1` or a later failed swap); all its GF readers (hart 1's stale iterations) realized | `d` top := 0 |
| k+1 | `A_d1′` (hart 1's successful acquire of `d`) | `wr`: co-pred `w″` latest (just landed), readers realized | lands |
| sym. | `L(w′)`, `A_b2′` | | |

No step is skipped, silent or stale; the only non-GF steps are the two landings.  `SBAcq.l1NoMember`'s cycle
(`p w′ < p A1 ≤ fl F1 < p w″ < …`) does not arise because `p w′` (the landing) is AFTER `F2`, not before `A1`.
Machine-checked: `SBAcqP.l1MemberP`.

**The UART chain** (`W10-K0-census.md` §3 / P0(b) §2; harts 2/1/3; `w‴` = `sleep_prepare`'s release of `P2.lock`,
`X` = THR store, `LSR₁` = `uartintr`'s LSR read, `R_y` = `release(cons)`, `A_y3` = the next `consoleintr`'s acquire,
`r3` = `holding+0x0` on `P2.lock`).  As §0 says, (R1) of `ioResidueGmo` makes this GF inconsistent, so the walk never
meets it; **P replays it lockstep WITHOUT (R1), using only the fabric arm (R3) — [R45.7], with hart 2's continuation
and hart 1's `acquire(tx)` that the first table omitted:**

| step | item | gate | member effect |
|---|---|---|---|
| 1 | hart 2 `I(w‴)` | `plain` | pending |
| 2 | hart 2 `A_tx` (`acquire(uarts[0].tx)`) | `wr` | lands (no drain: `w‴` stays pending) |
| 3–4 | hart 2 LSR read, `X` (THR store) | `fab` (MMIO, immediate, fabric order) | fabric |
| 5 | hart 2 `release(tx)`: `fence rw,w` (epoch bump, NO drain), `I(sw zero tx)` | `plain` | pending, epoch-after `w‴` |
| 6 | **hart 2 loops → `sleep_prepare` → `acquire(P2.lock)`: an exclusive read of the byte holding pending `w‴`** | same-address drain: **hart 2 BLOCKS on `L(w‴)`** (E6) | — |
| 7 | hart 1 `LSR₁` | `fab` (after `X` in fabric order) | fabric |
| 8 | hart 1 `consoleintr`: `acquire(cons)`, `I(R_y)` | `wr`, `plain` | lands; `R_y` pending |
| 9 | hart 3 `A_y3` (`acquire(cons)`) | `wr`: needs `L(R_y)` first — `land`: `R_y`'s co-pred's readers are hart 1's own, realized; its epoch predecessors are fenced (`release+0x16`) | `L(R_y)`, then `A_y3` lands |
| 10 | hart 3 `wakeup` → `acquire(P2.lock)`: `r3 = holding+0x0` | `rd`: source = `P2`'s acquire write, member-latest since `w‴` is pending | R = 1 = GF |
| 11 | hart 3's long arm: `holding+0x12` reads `lk->cpu` | `rd`: source = P2's `lk->cpu = &cpus[2]` store (issued before `w‴`; landed or — under the epoch buffer — possibly pending, in which case GF's source is the previous value, landed) | R = GF |
| 12 | hart 3 failed swaps (GF reads 1) | `wr`: co-pred latest, readers realized | land |
| 13 | GF's hart 3 next read of `P2.lock` returns 0 ⇒ gated on `L(w‴)` | `land`: every reader of `w‴`'s co-pred realized | **`L(w‴)`; hart 2 unblocks (step 6)** |
| 14 | hart 1's later `acquire(tx)` (in `uartintr` after `consoleintr`): if GF has it read hart 2's pending `sw zero tx` | waits on `L(w‴)` too (epoch order) — hart 3 does not wait on hart 1, so no cycle | after step 13 |

The MMIO store overtaking a buffered RAM store is the one freedom P has that the registered machine lacks and K
needed a skip for.  **P needs neither (R1) nor (R2) for this; it needs (R3) (fabric ⊆ gmo) for H4.**  [OWN.111]'s
premise is confirmed.

## 5. Increment plan (rev 58: rev 57's rows + results 2026-10-21 and [OWN.137]–[OWN.150]; the live sizes are the plan's REMAINING WORK; DONE rows kept for the record; **[rev 58] MCSL hours at A7's observed 12–20 h/k**)

Lanes: **MCSL** = the serial MachCSL lane (one editor; δ1 is closed at inc 16b, X1 and E4 merged, P0(c) done on a
scratch branch, so the lane is FREE for P-M1); **Weak** = parallel Weak-only slots.  Worker-hours at the observed rates
(MachCSL cone 6–10 h/k, Weak leaves 4–8 h/k) + acceptance.  Acceptance gate for every MCSL increment: `lake build
MachCSL Xv6 Weak Vtest` green, `audit.sh` (+ `--weak --build`) with baseline/opaques unchanged, `tcb.sh` (module set
moves at most once), statements of every registered root textually unchanged (diff of `#print` signatures).

| # | increment | lane | lines | h | depends | conf. | acceptance / notes |
|---|---|---|---|---|---|---|---|
| P0(a) | ~~P-WFENCE census~~ **DONE** (`notes/W10-P0a-wfence.md`, `ymqrrsuq`): P-WFENCE FALSE (`ip->ref` ×4 foreign-readable non-WCrel; 5 strict WCrel sites; `lk->cpu` acyclic reader-side; `initlock` unpublished; PTE stores chained given custody) → F-R45-1 → [OWN.112] | spike | 0 (note) | — | — | ✓ | the WCrel leaf is needed only under the FIFO fallback |
| P0(b) | ~~Lean checks~~ **DONE** (`Weak/LitmusSBAcqP.lean` 752 l., `twqyqmnx`): F-P1 CONFIRMED (`uCat`/`uIoNo`/`uNoR1Ok`), `l1MemberP` (Litmus 1 has a P member), δ1′ sufficiency 26/26 census sites (`l3Cat`/`l3NoMember`/`l3MemberT`: the racy `ip->ref` chain needs 6m's route-T datum under δ1′) → [OWN.111] | spike | 0 (752 l. landed) | — | — | ✓ | |
| P0(c) | ~~MachCSL churn spike~~ **DONE — PASSED** (w1 scratch, never merged: `vumrwzmr` core, `tvzktvuv`/`kynvprpl` `MachCSL/SpikeP.lean` 831 l. sorry-free; `PROGRESS-W11F.md` §6).  (1) `interp_land :537` PROVED over the minimal interpretation (merged-history heap + `lp` map with persistent `landedAt` certs + pure `mmOkP`), no client resource consumed, `readBytes_land :448`; (2) churn census A′: 27 MachCSL files, ≈ 411 errors (Wp 79, WpAtomic 77, WordHist 52, Resources 31, Lock 27, UIcache 25, WpStoreOrd 19, WpPtWalkOwn 17, KptInv 11, WpLock 10; ≈ 250 mechanical) + 319 position comparisons / 16 MachCSL files and 87 lines / 16 Xv6 files whose MEANING shifts (statements still type-check) — **go/no-go: GO** (statement churn in `ChainDefs`+`KptInv`+`Lock` well under the ≈ 120 threshold; `interp_land` client-invisible); (3) `memModel_issue :645` keeps the pushed postcondition, `wp_s_sw_core :718` (`wp_s_sw`'s statement does NOT break); (4) `read_casesP :784`/`read_cases_floorP :820`; (5) **`interp_landE :556` — the per-address + epoch buffer goes through, `landOk_landOkE :418` (FIFO is a special case); the epoch adds 0 errors → [OWN.113] CONFIRMED**; (6) `simStep` is `m ≤ 1` (§3.6); (7) the land arm is SILENT and absorbed once in `wpHart_lift_obsP` (§2.2).  **Measured MachCSL churn 6–10k** (+ the epoch token 0.3–0.7k, the merged-head `curWordAt` restatement, the `insLanded` AMO postconditions) | spike | 0 (831 l. scratch) | — | — | ✓ | the MCSL lane may commit |
| P-M1 | ~~`TsoMem`/`Lang` state + arms + δ1 RETIREMENT~~ **DONE — MERGED [rev 56]** (`lrqroyvv`, +1.04k/−1.64k; strict acceptance PASS 4,066 jobs): the route-P state and arms landed with an EAGER-landing staging (`landedEager`), δ1 deleted ([OWN.114]) | MCSL | 0 (was 0.6–1.1k) | — | — | ✓ | |
| P-M2 | ~~interpretation~~ **DONE — MERGED [rev 56]** (`uusvmmrl`, +1.6k/−0.2k): the `okP` invariant, **`interp_land` PROVED without staging** (the gate), lifting re-proved; `sbNil` staging kept | MCSL | 0 (was 1.1–2.0k) | — | — | ✓ | |
| P-M3 | ~~lifting + base memModel lemmas~~ **DONE as P-M3a+b — MERGED [rev 56]** (`ouznrlqo`, +1.1k): dual ops, Löb arms, `sbNil` kept; **F-P-M3-1: the flip is inseparable from the readers** → [OWN.122] | MCSL | 0 (was 0.8–1.4k) | — | — | ✓ | |
| P-M4 | ~~history layer + export sub-definitions over `lp`~~ **DONE as P-M4a/b/c — MERGED [rev 56]** (`uutlwtuz`, +1.54k): `FlatMem.lview`, `stepGrowP`, the export TWINS `xv6AccessDiscP :1547` (`lkCpuReadAtP :1467`, `ksFrameAtP :1539`) + the eager bridge | MCSL | 0 (was 1.5–2.8k) | — | — | ✓ | |
| **P-M5–8** | ~~THE SWITCH BRANCH ([OWN.122] (b))~~ **DONE — MERGED [rev 58]** (`qxqznmnr`, 2026-10-21 08:22: w1 DONE at CP-6z38 — RED 0, strict acceptance PASS in slot, 4,076 jobs; the patch `parked/switch-branch-CP6z38.patch` applied onto tip `unrmonww` in w2 with ONE integration fix (`SbHoldX`'s `NonHolderRd` over the new `lkCpuReadAtP`); TIP STRICT PASS 08:39 `tip-merge-switch.log`; I3′ + D17′ (`KptSeal.recordP_of`/`ptConjuncts_of`), F-11.7 closed; **the registered machine IS route P**).  Rev 57's description follows as the record — DONE on the branch (RED 39 → 12 → 0): the switch + flip (D1/D2), P-M5 as **D9** (numbers = landing positions, identities = issue stamps; `landCovAt`/`vecCertsAt`; the `landsAboveAtE` ghost — replaces D3 of rev 55/56), P-M6 (D4/D10 `lockRelReady`; F-11.2 `relInsOkM`/`exclRelOk`; the dynamic lock's ISSUE-STAMP window [OWN.134] + "registered by now" [OWN.125] + F-11.1e (b)), P-M7 (D11; D14 (c) disk; `memImg`), P-M8 so far: **the export FLIPPED** (`xv6AccessDisc` := the twins), **the [OWN.131] step guard in the machine** (`MachCSL/Lang.lean:1277-1296` on the branch: `drvOkPc`, `vqPagesPend`, `drvOkGuard` in `evStep`'s MMIO-write arm + `blockedStep`; rule `wp_s_sw_dev_drvOk`), [OWN.126]/[OWN.132] sub-definitions, [OWN.135]'s textual half (`kvmRootLandsLast` REMOVED, root text RESTORED), Weak D5 (`MachOfPf` `m ≤ 2` = P-W5's core), Vtest; measured **+11.9k/−5.8k vs the tip**.  LEFT: D12‴ step 3 (0.3–0.6k) → `DiskAcc` flip + D15 (0.4–0.8k) → DESIGN I3 the readers (0.8–1.3k) → DESIGN D17 the three page-table REDs under [OWN.135] (**1.1–1.7k**, was ≈ 0.3k) → Weak cascade + re-measure (0.3–0.8k) → docs (`LinkDiscAdequacy` header: [OWN.131] the ONLY named assumption; REVISIT [OWN.124]) + THE strict acceptance (0.1–0.3k).  NO load-side item enters the branch | MCSL | **0** (was 3.0–5.5k LEFT; total ≈ 15–17.5k gross vs 5.3–9.8k est.) | 0 | P-M4 ✓ | ✓ | PASSED: all registered roots re-proved, statements unchanged (the [OWN.135] restoration included), `tcb.sh`, `audit.sh` baseline/opaques unchanged; lint/audit/`audit --weak --build`/tcb all 0 |
| **Q1–Q9** | **the serial MCSL QUEUE** (plan REMAINING WORK rows Q1–Q9; **[rev 58]: Q1 DONE** — inc 1 `yywrnzvn` (`MState.kArm :131`, `kExcWrite :1339`, `kStuck`) + [OWN.143] F1 `ovwowpkvwtuk` (`fence.i`'s `itv` joins `rv`) + Q1-c (E2) [OWN.144] (`Weak/CapFetchOfs.lean` 428, `CapFetchCyG.lean` 642); **Q2 → Q3 → Q4 RUNNING w1 since 18:31**; **Q5–Q7 ON HOLD — CONDITIONAL on the S-R `DomAt` lift [OWN.150]**; Q9 gains [OWN.145] (s-a) the per-hart "interrupts off" ghost record +0.4–0.8k; row 6c's OWN instrument (F-Q1-5, +0.3–0.8k) joins the lane after Q4): ~~Q1 [OWN.115] stuck-on-kernel-fault (+ `spinFenceNext` fold-in) 0.5–1.5k~~; Q2 M13 `acqExclOk` + clause 13 `lockNzExclAt` [OWN.118] 0.4–0.9k; Q3 walker A/D + DMA `pcAt` −2 stamp 0.1–0.2k; Q4 [OWN.119] load-pc ghost + export 0.3–0.7k; Q5 M12-a 0.3–0.7k; Q6 M12-b 0.4–0.8k [OWN.117]; **Q7 (r1) frame-quiet `∀ j a, ksLiveFrameAtP σ j a → ∀ i ≠ j, ∀ e ∈ σ.sb i, ¬ e.hits a` + (r2) `LkCpuQuiet` (PROGRESS §HEADHOP (a2-lkcpu)) — additive interpretation records on the route-P state [R46.5], 0.5–1.1k**; Q8 `csIssue` export (F-P-W4-1) 0.2–0.4k; **[rev 57] Q9 [OWN.136] the per-hart "release armed" flag (set by `fence rw,w`, cleared by any explicit store/AMO/trap; every release-pc store happens with it set, `LockFacts.relAdj :113`), exported APPEND-ONLY, replaces row 6e's `relRunRealized`; after P-W6/Q1; 0.6–1.4k** | MCSL | **3.2–7.0k** (= Q2–Q4 0.8–1.8k + Q5–Q7 1.2–2.6k + Q8 0.2–0.4k + Q9 1.0–2.2k; **2.0–4.4k if S-R lands**; estimates except Q7/Q9) | 38–140 (24–88 if S-R lands) | P-M8 ✓ | M | each an append-only export / additive record; `tcb/expected.json` unchanged |
| **P-W1** | ~~`SbCand` …~~ **DONE — MERGED** (`zsqxzoqp`: `Weak/SbCand.lean` 751 l. — `SbEnt`, `SbPol` four laws, `SbPol.epoch` primary / `SbPol.fifo` fallback / `SbPol.leEpoch`, `execWfP`, `execWfOfOld`; `Weak/SbCandLit.lean` 136 l. — `l1MemberSb` under every lawful policy; `LitmusSBAcqP` §5 (+134 l.) — `l4Cat`/`l4NoMemberP` (policy-independent)/`l4MemberX`; `Weak.lean:804-805`).  Findings: **F-P-W1-1** (the AMO's epoch guard, adopted), **O-P-W1-a** (`LFence false×4` = `fence.i` AND the `sfence.vma` marker → P-W6 fetch marker); forwarded-byte label timestamps → P-W2 | Weak | 0 (1,021 l. landed) | — | — | ✓ | |
| P-W2 | ~~`SbWalk`/`SbReplay`/`SbAgree`~~ **DONE — MERGED [rev 56]** (`xvqkutzu`/`kqnxzksy`/`otywpvqr`; 2,763 l.): `agreeX`/`agreeW3OfX`/`agreeW4OfX`, `memberGwf`, the read arms (`loadArm`, `rdXArm :705`), `valEqX :744`, `ipRefTaint :75`/`ipRefRule :90`, `memberFwdSrc`, `lockBlk`; findings F-P-W2-1 (`irefGe1` not GF-provable → `IrefGF`/`IrefTop` NAMED → M12-a/b), F-P-W2-2, F-P-W2-3, O-P-W2-a | Weak | 0 (was 1.0–1.8k) | — | — | ✓ | |
| P-W3 | ~~THE GATE + `noStuckP`~~ **DONE modulo its NAMED INPUTS — MERGED [rev 56]** (`LitmusSbStuck` 361, `SbOrd` 1,269, `SbOrdWalk` 757, `LitmusSbStuck2` 239; heads `qxwpnplt`): `noStuckP :1202` modulo `HeadOrd`; H1/H2/H4/H5 PROVED (H4 by (R2″) [OWN.116]); H3 = `HeadOrdRd :251` with (a1) static hops (`SbHeadHop` 306) and (A2) windows (`SbHeadHop2` 551) PROVED; `DevStOrd` DERIVED (`SbDevSt` 587); residue = the per-site named inputs (rows P-W3r below) | Weak | 0 (was 1.3–2.4k) | — | — | ✓ | |
| P-W4 | ~~kill glue~~ **DONE — MERGED [rev 56]** (`wknttmlq`, `SbKill` 564): class-blind transport (F-6b′-1 (A)), `acqAq`/`relCovers` at the member (6f absorbed), `certSupplyP :461`, `l2ClaimP :507`, `cycleKillAllP`; F-P-W4-1 `csIssue` NAMED → Q8 | Weak | 0 (was 0.8–1.4k) | — | — | ✓ | |
| **P-W3r-a** | ~~the `holding+0x12` exemption~~ **DONE — MERGED [rev 57]** (`wlroyyto`; `Weak/SbHoldX.lean` 280: `holdCpuX :65`/`exemptX :71` — exempt ONLY inside `acquire`, `ra = acquire+0x16`; `holdCpuTaint :81`, `holdCpuShape :100`, `holdCpuRule :155`; the member side `CpuTop` from the P-W6 interface `CpuTopMap` + `lkCpuReadAtP :1467`) | Weak | 0 (was 0.6–1.2k) | — | — | ✓ | **`REVISIT [OWN.124]` in the docstrings `:6,60,252`**; (b) on file |
| **P-W3r-b** | ~~`HoldZero`~~ **DONE modulo (Z1)–(Z3) — MERGED [rev 57]** (`wlroyyto`; `Weak/SbHoldZero.lean` 266: `cpuNeOfFloor :121`, `holdZeroOf :246` ⇒ `SbHeadHop2.HoldZero :481` from `CpuWordWin :68`/`CpuFloor :75`/`NotHolder :81` → P-W6/6n) | Weak | 0 (was 0.6–1.2k) | — | — | ✓ | no MachCSL record |
| **P-W3r-c** | ~~`blockedIsCensus`~~ **DONE — MERGED [rev 57]** (`kqsppmrw`; `Weak/SbBlocked.lean` 838: `EpochOk :264`/`DrainOk`, `Hb`/`hbSound`, **`blockedIsCensus :782`**, `headOrdRdOfCensus :819`; F-W2-BC-1) | Weak | 0 (was 0.5–1.0k) | — | — | ✓ | `drainLanded` is a THEOREM here (DR), not a `PInv` clause |
| **P-W3r-d** | ~~the LB-freedom census leaf~~ **DONE — MERGED [rev 57]** (`kqsppmrw`; `Weak/SbLbFree.lean` 131: `lbFreeStatic :70`, `holding12FrameOnly :104`, `ismapped10RetFree :119`; **F-W2-LB-1** `uvmclear+0x10`'s point is a `PDep` store — a third LB-not-excluded site, never blocked) | Weak | 0 (was 0.05–0.15k) | — | — | ✓ | `decide +kernel` |
| **P-W3r-e** | ~~`drainLanded` + `DiskDesc` + `VirtioIdx` + `VirtioDesc`~~ **DONE — MERGED [rev 57]** (`skyowwlm`; `Weak/SbVirtio.lean` 407: `CtrLanded :69`, `Hv`/`hvSound :115`, `srcGateOfClsV :172`/`valGateOfClsV :200`; the inputs STATED + consumed `DiskDesc :290`/`VirtioIdx :303`/`VirtioDesc :315` → P-W6; **F-W2-V-1** → `SbOrdWalk.gatedW :597` (a), `ozrqruqw`) | Weak | 0 (was 0.7–1.5k) | — | — | ✓ | |
| **P-W3r-f** | ~~`HeldPin`~~ **DONE — MERGED [rev 57]** (`xuorxlsx`; `Weak/SbHeldPin.lean` 364: `valGateOfWin :108`, `HeldWinGF :227`, `heldPin :239`, `heldNeverBlocked :298` over `HeldCtx :292`; **F-W3r-f-1**: a GF-level lock-word WINDOW, not the realized-prefix pin — a spinner's failed swap may be unissued) | Weak | 0 (was 0.1–0.3k) | — | — | ✓ | |
| **P-W3r-g** | ~~PTE custody at the realized prefix~~ **DONE — MERGED [rev 57]** (`xuorxlsx`; `Weak/SbPteCust.lean` 247: `acqHop :84`/`relayAcq :93`, `PteCustSrc :117`, **`pteNeverBlocked :122`**, `walkerSrcLatestC :208`; landed WITHOUT P-W6) | Weak | 0 (was 0.3–0.6k) | — | — | ✓ | |
| **P-W3r-h** | **`FrameQuiet` + `LkCpuQuiet` Weak glue** from Q7's records through P-W6 (`SbHeadHop2.FrameQuiet :494`) | Weak | 0.2–0.4k | 1–3 | Q7, P-W6 | M | the last P-W3r row |
| P-W5 | registered W4 re-proof — **its CORE LANDED with the branch (D5: `MachOfPf` `m ≤ 2`, `PfStepTso*`, buffer empty between pf steps) [rev 58]**; what stays: M1/M2 re-registration, `audit --weak --build` 13 roots green | Weak (**LAUNCHABLE** — P-M8 merged) | 0.3–0.8k (was 0.8–1.5k) | 1–6 | P-M8 ✓ | M+ | `audit --weak --build` 13 roots green |
| P-W6 | buffered twin W4-P — **[rev 58] the SPIKE LANDED `wokqvokp` (`Weak/SbRealP.lean` 1,196: `rmemP :71` + the MEMORY ROWS, `rmemPLand :565` GIVEN `ForeignBelowLanded :430`; F-PW6-1 both sides `landBlockedForeign :1145`/`wit1Run :1176`); PAUSED [OWN.147], RESUMED [OWN.149] after the conformance matrix (plan row CM), rows in the matrix's order; LEFT (`PROGRESS-PW6.md` §3): `IssueCo` 0.2–0.4k + census 0.5–1.2k, the [OWN.148] device-row drain gate 0.4–0.9k (edits `SbOrd.enbL`, descent via H4 `stOrd`), DMA rows 0.15–0.3k, hart rows 0.8–1.5k, `SimRelP`/`simRunP`/`recRealizedP` 0.4–0.8k, CapF6–10 `readAt` 0.3–0.6k, transport residue 0.3–0.8k, `fence.tso`/`FetchCutP` 0.1–0.2k; + `CapDataOk.cycReal` with `PC` (6d).**  Was: (`rmemP`: `R-sb` (+epochs), `R-lp`), `recRealizedP`; CapF6–10's `readAt` at the member (feeds 6b, 6j E1); **+ a distinct fetch marker for `fence.i` vs the `sfence.vma` marker (O-P-W1-a)**; **+ (T) the label↔pc transport and the state map the per-site inputs read through (`lkCpuReadAtP`/`lockWordDiscAtP` at the top; issue stamps vs `gwix` landing positions — 6a's note)**; **[rev 57] + the P-W3r TRANSPORT RESIDUE: `CpuTopMap`, `CpuWordWin`/`CpuFloor`/`NotHolder`, `HeldCtx`/`HeldWinGF`, `PteCustSrc`/`WalkerCustSrc`, `CtrLanded` + `DiskDesc`/`VirtioIdx`/`VirtioDesc`, `CapFrame.floorByteReal` (+0.3–0.8k)** | Weak (w2) | **3.2–6.7k** (was 1.9–3.6k; 1.2k landed) | 13–54 | P-W5, P-W2, CM | M− | `segRealized`/`readAt` at `SbCand` members; **K1** (> 2k unplanned MachCSL or a per-load footprint record) |
| **P-W6-f** | **[rev 58] NEW** `FetchProg` (`SbProg.lean:194`, F-6m-1): the fetch-progress input — discharged with P-W6's fetch marker (O-P-W1-a) through the state map; ledger row 2's bridge | Weak | 0.4–0.9k | 2–7 | P-W6 | M | coordinator-provisional (a) interim |
| **CM** | **[rev 58] NEW — the twin↔machine CONFORMANCE MATRIX [OWN.149] (a), A7 §5.1** (w2, RUNNING since 18:31): ≈ 9 twin rules (`SbCand.stepE` load/issue/fence/rmw/io, `SbCand.land` + `SbPol.epoch`, boot, the device row, fetch = the admin star at view 0) × ≈ 14 machine arms (`evStep`: memRead MMIO / ifetch `Lang.lean:1562` / plain `:1565-1567` / exclusive; memWrite MMIO / issue / exclusive; barrier; land `:453`; `blockedStep` ×3; `storeDma`/`devStep`; no-ops); cells EQUAL / twin weaker / machine weaker / outside spec + the realization premise per gap; a 2-hart litmus (`decide +kernel`, ≈ 40 l.) per "machine stronger" cell; deliverables `notes/twin-machine-conformance.md` + `Weak/SbConfLit.lean`; feeds P-W6's row order and the plan's LEDGER | Weak | 0.1–0.5k (est.) | 8–16 | P-W6 spike ✓ | M+ | **K2′**: a gap NOT in the matrix after the audit |
| **S-R** | **[rev 58] NEW — the `DomAt` lift [OWN.150] (i)** (w3, RUNNING since 18:31; `parked/PROGRESS-SPSR-1021.md` §4): `DomAt` preservation lifted from `WeakAxiomatic3.lean:26-33` to the buffered twin 1.5–3k; progress re-proof with reads not waited on 0.4–0.8k; the S-R arm in `SbOrdWalk` 0.2–0.4k; re-plumb 0.3–0.6k; deletions −0.3–0.6k.  FAITHFUL (cat's load-value rule).  **If it lands: retires Q5/Q6/Q7, P-W3r-h, the two `ip->ref` exempt pcs [OWN.112], N3/N4, half of H3 — NOT [OWN.124], NOT F-6h-1**; re-opens ≈ 4k of landed walk files | Weak | +2.1–4.2k (MCSL −1.2–2.6k) | 10–35 (net ≈ −40 to +20 h) | P-W3 ✓ | M− | **K-DomAt**: > 3k or an xv6-specific fact ⇒ stop, build Q5–Q7 |
| **Σ P** (rev 58) | | | **8.1–17.5k if S-R lands** (MCSL 2.0–4.4k serial = Q2–Q4 + Q8 + Q9(+s-a); Weak 6.1–13.1k = P-W5 0.3–0.8k + P-W6 3.2–6.7k + P-W6-f 0.4–0.9k + CM 0.1–0.5k + S-R 2.1–4.2k) **∣ 7.4–16.3k if S-R is killed** (MCSL 3.2–7.0k; Weak 4.2–9.3k incl. P-W3r-h 0.2–0.4k); since rev 57: the branch 3.0–5.5k + Q1 0.5–1.5k LANDED, P-W6 +1.3–3.1k, P-W6-f/(s-a)/CM/S-R appeared | **≈ 58–206 ∣ 63–226** | | **M** (P-W6, S-R M−) | |

Order ([rev 58], [OWN.149]/[OWN.150]): **w1 the MCSL queue** Q2 → Q3 → Q4 → Q8 → Q9 (+ s-a [OWN.145]) → 6c's instrument (F-Q1-5) → Q5–Q7 ONLY if S-R is killed;
**w2 the conformance matrix (CM, 1–2 days) → P-W6** with `IssueCo` + census and the [OWN.148] gate, rows DMA → hart rows → `SimRelP` → `readAt` → transport residue
→ `FetchCutP` (+ P-W6-f); **w3 the S-R `DomAt` lift** (kill > 3k) → then `Weak/SbIssueCo.lean` if w2 has not reached it, or (t3) [OWN.139] if the owner puts it inside
the capstone; P-W5 (re-registration) is LAUNCHABLE now; after P-W6: 6c/6d consumers → 6e (after Q9) → 6j → 6n → 7 → 8; weeks 3–6 (A7 §5.2): 6j, 6n, 7, 8.  **After the
capstone (plan rows A5–A9): (t3) → R-PF′ (G2-S item 0) → M-S2 (`fence.i` non-draining + forwarding + T4/O1 restated) → SAIL-GAP-1 / A4 → G2-S (recorded order + Theorem S) →
G2-SC with S-K if a second RVWMO theorem is planned.**  Kill criteria K1, K2′, K3, K4 (did not fire at rev 58), K5, K6, K-DomAt per A7 §6.  The rev-57 order follows as the record.
Order ([rev 57]): **finish the switch branch** (w1 from CP-6z27: D12‴ step 3 → `DiskAcc` + D15 → I3 → D17 → cascade → docs → THE strict
acceptance = P-M8; ≈ 1–3 calendar weeks) → the queue Q1 → … → Q8 → Q9 [OWN.136] ∥ **w2 row 6h + w3 row 6m now** (Weak-only, against the
tip); after Q1: 6c → 6d; after P-M8: P-W5 (re-registration) → P-W6 (+ the P-W3r transport residue) → P-W3r-h (after Q7) → 6e (after Q9)
→ 6j → 6n → 7 → 8; after the capstone: A4.  **The ONLY named xv6 assumption is [OWN.131]** (§6).  The rev-56 order follows as the record.
Order ([rev 56]): **the switch branch now** (w1; [OWN.122]; released by [OWN.123]/[R46.5]) → P-M5 → P-M6 → P-M7 → P-M8
(ONE strict acceptance; ≈ 3–6 calendar weeks of one slot) → the queue Q1 → … → Q8 ∥ **P-W3r-a + P-W3r-b (w3) and
P-W3r-c + P-W3r-d (w2) now** → P-W3r-e/f ∥ the unaffected rows 6e/6g/6h/6m (plan REMAINING WORK); 6c/6d after Q1;
P-W5/P-W6 after P-M8, then P-W3r-g/h, 6j, 6n, 7, 8.  Row 6m under P = the three-pc taint's Sail meaning (O-P-W2-a,
inside P-W3r-a) + the lockstep-datum glue 0.3–0.8k; the chain-based race-free-read theorem (6m F6) is retired (`valEqX`
is it).  Riskiest steps now: **the branch's flip + P-M6** (the release/`started` rules consuming the epoch token; the
`insLanded` AMO postconditions; one long red stretch) — M−; `noStuckP`'s residue is M (finite table, mostly proved mod
(T)).  **Rejected by R46 ([OWN.123])**: (P+L) a load side in the twin only (a blocked head realized EARLY with GF's value —
W4-P must then REORDER, the (R) rescheduling the owner rejected for δ1 [OWN.103]; +3–6k Weak / 25–50 h, M−/L; the value
interfaces are NOT saved); (M+L) a load side in MachCSL (loads from unlanded foreign stores / promises; +10–25k / 80–200 h
inside the red branch, L — the WP load rules would return values no history holds, breaking the merged-history ghost
§2.6; theorem UNCHANGED in meaning since LB is unreachable for this binary).

## 6. Published statement, trusted base, registered roots

* **T-alloc-RVWMO statement text (§A of the plan, `srvwmoXv6M2` + conclusion (b)): UNCHANGED.**  The quantifier is
  `rvwmoCatConsistentT ∧ ioResidueGmo ∧ xv6ConfS`; the conclusion speaks of "the realizing MachCSL run"; which machine
  realizes is proof content.  **Trusted base: UNCHANGED** — MachCSL is a proof device for T-alloc-RVWMO (confirmed:
  `MachCSL.*` appears nowhere in the published premises; it enters only through the registered MachCSL-tier roots
  the conclusion cites).  No new named premise; `noStuck` NAMED only as the fallback of P-W3 (WEAKER, [R44.7]).
  **[rev 57] ONE named xv6 PROGRAM-STEP assumption, and only one — [OWN.127]/[OWN.131], xv6 weak-memory BUG #1
  (`notes/xv6-weak-memory-bugs.md`; found by the branch, F-11.5):** `virtio_disk_init` zeroes the three queue pages
  (`+0xf0/+0x102/+0x10c`) and then stores `QUEUE_READY` (`+0x14a`) / `DRIVER_OK` (`+0x170`) to MMIO with NO fence; RVWMO +
  PMAs order a RAM store before a later MMIO store only through `fence w,o`, so a polling device may read `kalloc` junk
  (not observable on QEMU-TCG).  Form (G): a STEP GUARD of the proof machine — hart 0's `DRIVER_OK` store waits until the
  three `memset`s have landed (`MState.drvOkGuard`, `MachCSL/Lang.lean:1292` on the branch, in `evStep`'s MMIO-write arm and
  `blockedStep`), as if a fence were there, at that one instruction only — STRONGER than RVWMO at that instruction, EQUAL
  everywhere else; kernel unchanged ([OWN.4]).  Because it is on the MACHINE, every registered root (SC-tier included) is
  stated over the guarded machine; no root's statement text changes; documented in `LinkDiscAdequacy`'s header, the roots'
  docstrings, the bug list and the final theorem's docstring (rows P-M8/8).  Bugs #3 (kvminit root store) and #4 (pipealloc
  lock words) were PROOF GAPS — xv6 is safe there — and were WITHDRAWN with their premises ([OWN.135], [OWN.134]); the
  general rule [OWN.129] (bug-like ⇒ record + a step-scoped named assumption; fix the code later) stands for future findings.
  **[rev 57] Named PROGRAM facts (not xv6 bugs; proof premises until A1/A2): `excRetR` [OWN.96], `fetchLateChained` [OWN.101], and
  now `fetchReplayOk`'s EARLY E2/E3 half [OWN.137] (row 6h F-6h-1: no replay proof under P without O2's lock-hand-off argument;
  REVISIT item 3, "fix later"; retires with A2, +0.3–0.8k).  [OWN.138] (r1) makes `fetchReplayOk` TRUE again on RWX user pages by
  a separate own-hart arm for the fetching hart's po-later writes (FAITHFUL; a no-RWX premise rejected).**
  **[rev 58] Landed: `G7FetchOwn.fetchEarlyForeign :53` (NAMED, REVISIT [OWN.137]), `ownLateE3 :72`/`ownFencedNone :89` (the (r1) arm, PROVED).  F-6h-3 → [OWN.139] (t3): the two
  own-hart RWX corners are to be PROVED unreachable in xv6 (~2–4k Weak), NOT named, NOT excluded by a premise, NOT closed by a stronger `fence.i` rule (plan row A5).  NEW named inputs
  of the day (proof premises until their rows land, WEAKER while named; none in the published statement): `SbProg.SailX :173` (the three-pc taint's Sail meaning, N13), `SbProg.FetchProg
  :194` (fetch progress, N14 → P-W6-f), `IssueCo` (the walk's same-byte issue order, N15 → P-W6, census), `CapDataOk.cycReal` (the state map at the member, N16 → P-W6).  The `fence.i`
  DRAIN is documented STRONGER than Zifencei (EX-FENCEI-1) and kept until M-S2 [OWN.146]; (R1) is kept until A4/A8 as the compensation for SAIL-GAP-1 [OWN.142] (the published header
  says "a QEMU-like platform for MMIO").  What the expert reads of the published text under R-H (A7 §3.4): "every riscv.cat execution of this image satisfies the invariants and
  allocproc's answers; the proof machine has RVWMO's store side plus FIVE documented strengthenings, each proved harmless for this binary; named platform/device texts; three REVISIT
  items; one xv6-bug assumption" — quantifier FAITHFUL, machine STRONGER where documented.**
  **[R45.7] Of `ioResidueGmo`'s arms the replay uses (R3) and — since P-W3 (F-P-W3-2, [OWN.116]) — the NEW (R2″) (H4/Efab:
  an I/O access po-before a later RAM read is gmo-before it, `GraphFabResidue.ioResidue :123-138`); (R1) is NOT used by
  P.  [rev 56] (R2″) is trusted platform text STRONGER than RVWMO + PMAs, owner-ruled to be removed with (R1) in A4
  (REVISIT list item 2); the published statement's header is otherwise unchanged, and the `holding+0x12` exemption
  [OWN.124] is named in `LinkDiscAdequacy`/`RvwmoXv6Adequacy`'s documentation as REVISIT (row P-M8 / row 8).**
* **The registered MachCSL-tier roots** (`tools/ci/roots.txt`: `MachCSL.riscvPowerAdequacy`,
  `Xv6.xv6FsAdequacy_closed`/`_xv6GF`, `userProof`, `unionAdequacyClosed`, `unionSyncCutNeg`, `unionResults`,
  `xv6NiAdequacy`/`TwoRun`/`TwoRunObs`/`StrongInstance`/`Out`/`Prefix`/`Det`, `xv6TextAdequacy_closed`,
  `xv6DiscAdequacy_closed`): statement TEXT unchanged, the MACHINE they quantify over changes (`primStep`'s arms) —
  the [OWN.105] precedent: every root re-proved, strict audit (`audit.sh`, `baseline.json` opaques expected
  unchanged: the two `resv` opaques, `bootImageSealed`, …), `tcb/expected.json` module set unchanged if no new module.
  For THESE roots MachCSL's memory model is the model being assumed, so their meaning moves from "TSO" to "RVWMO's
  store side" ([OWN.113]; **[rev 58] NOT exactly — the plan's STRENGTHENING LEDGER has FIVE rows: the exclusive read's
  same-address drain, the `fence.i` drain ([OWN.146]), no ifetch forwarding, no load buffering ([OWN.123]), and — found by the P-W6 spike,
  F-PW6-1 — cross-hart same-byte plain stores landing in ISSUE order, because §2.1's `pendOne` rule was never implemented; the last goes
  with R-PF′ after the capstone, the first two with M-S2**) — a documented strengthening of what the kernel
  proof covers.
* **Weak roots** (`roots-weak.txt`): M1/M2 (`srvwmoXv6M1Core`, `srvwmoXv6M1`, `srvwmoXv6M2`) re-proved via P-W5;
  the ten AxSpin roots import `MachCSL` (`Weak/AxSpinT2b.lean` etc. through `WeakMem`) but use neither `evStep` nor
  `TsoMem`'s read functions — expected unaffected; re-audited by `--weak --build` as a matter of course.
* `Xv6.xv6DiscAdequacy_closed`'s docstring/export sub-definitions move (§2.5); the conjunct list does not.
* **After-capstone item A4 — drop the HART-side (R1) ([R45.7]; plan REMAINING WORK A4; 1–2.5k, 8–20 h, M; after
  P-W3, on the W11-B re-route).**  Inventory of the remaining uses of (R1) (sizes unverified):

| # | use | file:line (tip) | what replaces (R1) | size |
|---|---|---|---|---|
| U1 | the I/O-window entry `entry <gmo x`: `ioSegPinned` (W13 (K) §7 "Claim L-IO"), `gpoOfGmo` ("a same-hart write gmo-after `x` is po-after it"), `ioSegAfterIoC`, `ioWinRelGmo`/`ioSegCertRrC` (W11-B re-route) | `WeakRvwmoKillIO.lean:612-650` (`ioSegPinned :626`), `WeakRvwmoKillIOC.lean:311` (`gpoOfGmo`), `:466` (`ioSegAfterIoC`), `CatRerouteIo.lean:60-70` (`ioWinRelGmo`) | the re-route needs only `entry <gmo REL`: the device lock's release `fence rw,w` (rule 4) gives it at every release site without `x`; `gpoOfGmo`/`afterIo` is the (K-cat′) closing-step invariant W11-B made unnecessary for the published route — verify dead, else M | 0.3–0.8k (+0.5–1k if `afterIo` is live) |
| U2 | `CertZ17` NF3/NF4 anchors (fabric-member RAM write before later lock-byte writes) | `CertZ17.lean:21`; consumed through `lockDiscCZ3` at `SilClose.lean:221,251`, `SilKillT.lean:241,297`, `SilSiteStep.lean:253,1080,1110` | **[R45.7-alt]** 0 — but because P RETIRES the whole `Sil*` kill chain that takes `lockDiscCZ3`/`orderSupplyCZ3` (§3.5), NOT because "6l removed them": at the tip they are still hypotheses of `SilKillT.cycleKillS`/`cycleKillZS` (`:211,241,269,297`); `SilOrd2`'s docstring (`:37`, `:1287`) only says ITS route does not need them | 0 |
| U3 | the DISK row (`y.1 = NCPU`): DMA reads po-before START/POP | `GraphFabResidue.lean:12-18` | device-MODEL semantics, not ISA: keep as a disk-row-only arm `(R1-dev) … ∧ x.1 = NCPU` — a trusted-text split, re-audit | 0.1–0.2k |
| U4 | `linCandDiskLat`/`ancOkIO` (W11 (iv)c) | `RvwmoXv6ScaT.lean:857-872` | consumes the disk-row arms + `gdiskRead14`: unaffected by dropping the HART-side (R1) | 0 |
| U5 | premise plumbing + (R3) for fabric progress/anchors: `SilOrd2 :561,611,1185`, `CertZ23`, `GraphFetchN2/WalkZ/Kill/AncSupply`, `CapFetchProv :121-243`, `LockFacts3 :181-255` | — | unchanged (they pass `ioResidueGmo` down and use (R3)/(R2)) | 0 |
| U6 | ≤ 2 mentions each: `CertZ15/16/19/25`, `SilWalk2`, `SilSiteStep`, `SilKill(T)`, `CertZ3/7/9/31/33/34`, `WeakRvwmoTopo/Acyc`, `GraphFabConf`, `PfStepTsoView` (42 files take `ioResidueGmo`) | grep | to be inventoried arm by arm (most are `ioResidueGmo` as a hypothesis name) | 2–4 h |

  (R2) and (R2′) stay (also stronger than the ISA; not P's business).  **[R45.s3]** With D48 (i/o fence bits dropped)
  NO in-tree site is ISA-given — all of (R1) is platform text today; the plan's §B(11b) sentence is corrected.

## 7. Σ remaining and % done (rev 57; see the plan's REMAINING WORK for the live table)

**[rev 58]**  Since rev 57 (2026-10-21 00:45 … 18:48): THE SWITCH BRANCH MERGED (`qxqznmnr`; ≈ +12.5k gross incl. its finish from CP-6z27 — the rev-57 "3.0–5.5k left" consumed);
Q1 DONE (inc 1 + [OWN.143] F1 + Q1-c: `CapFetchOfs` 428 + `CapFetchCyG` 642); 6h inc 1 `G7FetchOwn` 113; 6m `SbProg` 542; 6d's data half `CapDataTrap` 380 + `CapDataOk` 486; the
P-W6 spike `SbRealP` 1,196 — Weak +4.0k; ≈ **+16.5k gross** in all.  Became VISIBLE: P-W6's true size 3.2–6.7k (`IssueCo` + census 0.7–1.6k, the [OWN.148] gate 0.4–0.9k, DMA
rows, F-PW6-1/2), P-W6-f `FetchProg` 0.4–0.9k, Q9's (s-a) 0.4–0.8k, 6c's instrument 0.3–0.8k, the conformance matrix 0.1–0.5k, the S-R lift 2.1–4.2k (in place of Q5–Q7 +
P-W3r-h 1.4–3.0k if it lands).  Under P now: Q2–Q4 0.8–1.8k + Q8 0.2–0.4k + Q9 1.0–2.2k (MCSL) + P-W5 0.3–0.8k + P-W6 3.2–6.7k + P-W6-f 0.4–0.9k + CM 0.1–0.5k + S-R 2.1–4.2k (Weak)
= **8.1–17.5k** ("S-R lands") ∣ 7.4–16.3k ("S-R killed", Q5–Q7 + P-W3r-h instead); the rest 6c 1.1–2.3, 6d 0.1–0.3, 6e 0.7–1.4, 6j 0.8–1.6, 6n 1–2.5, 7 0.4–0.8, 8 0.1–0.2 = 4.2–9.1k.
**Σ remaining ≈ 11.6–26.6k (mid ≈ 19k; rev 57: 13.4–28.1k / 21k); ≈ 80–300 h (mid ≈ 190 h at MCSL 12–20 h/k — A7's observed rate — and Weak 4–8 h/k; the MCSL lane ≈ 1–3
calendar weeks, + 1–2 if S-R is killed; Weak ≈ 3–6 weeks at 3 slots).**  (t3) [OWN.139] 2–4k is listed AFTER the capstone by the coordinator (plan row A5) while A7 §3/§5.2 counts
it inside — with it, Σ = 13.6–30.6k; A7's raw R-H 18–38k minus what landed (4.3–8.8k) ≈ 13.7–29k agrees.  K4 did not fire.  DONE recounted at the tip by the rev-53 diff method
(plain `diff -ruN` against `~/dev/xv6iris` @ `802a9ab13`, EVERY `Weak/Ax*.lean` excluded, NO git/jj; the branch now IN): **+147.6k gross / −10.6k removed / +137.1k net** (MachCSL
+34.2k, Xv6 +14.6k, Vtest +0.5k, Weak non-`Ax` +98.3k).  **% done by lines ≈ 147.6 ÷ (147.6 + 19) ≈ 89 % (range 85 % at 26.6k remaining … 93 % at 11.6k); net 137.1 ÷ (137.1 + 19)
≈ 88 %**; counting (t3) inside ≈ 87 %; counting the after-capstone fidelity items A1/A2/A4/A5/A6/A7 (mid 22.2k) ≈ 78 %.  Read with care: the remaining ≈ 11 % is now mostly Weak work in
parallel slots (P-W6 the largest row, M−; S-R a killable bet), the serial MachCSL lane down to 2.3–5.2k (+ Q5–Q7 1.2–2.6k if S-R is killed); ≈ 2.7k (CertZ24–34) + ≈ 4–6k of `Sil*`
consumers are counted as done but superseded-but-green; three machine-STRONGER findings arrived in one day (A7 §1.1) — the rate K6 watches.

**[rev 57]**  Since rev 56 (2026-10-19 17:53 … 2026-10-21): seven P-W3r rows + row 6g LANDED (`SbHoldX`/`SbHoldZero`/`SbBlocked`/`SbLbFree`/
`SbVirtio`/`SbHeldPin`/`SbPteCust`/`CapFrame`, 3,121 l. + ≈ 70 modified ≈ **+3.2k gross**, against 2.9–6.0k planned); the switch branch
advanced CP-6d → CP-6z27 (RED 39 → 12; export flipped; [OWN.131] guard in the machine; [OWN.134]/[OWN.135] landed in part) at a measured
**+11.9k/−5.8k UNMERGED** — above rev 56's 5.3–9.8k for the whole branch — with **3.0–5.5k left** (D12‴ step 3, `DiskAcc` + D15, I3
0.8–1.3k, D17 1.1–1.7k, cascade, acceptance); row 6e's MachCSL half became Q9 [OWN.136] (+0.6–1.4k); P-W5 shrank under D5 (−0.5..−0.7k);
the eight leaves' NAMED realization interfaces moved into P-W6 (+0.3–0.8k).  Under P now: the branch's remainder 3.0–5.5k + Q1–Q9
3.3–7.7k (MCSL) + P-W5 0.3–0.8k + P-W6 1.9–3.6k + P-W3r-h 0.2–0.4k (Weak) = **8.7–18.0k**; the rest 6c 0.8–1.5, 6d 0.4–0.8, 6e 0.7–1.4,
6h 0.2–0.5 (RUNNING w2: [OWN.138] (r1) + the [OWN.137] naming; the early half → A2 +0.3–0.8k), 6j 0.8–1.6, 6m 0.3–0.8 (RUNNING w3), 6n 1–2.5,
7 0.4–0.8, 8 0.1–0.2 = 4.7–10.1k.  **Σ remaining ≈ 13.4–28.1k (mid ≈ 21k; rev 56: 18.9–38.5k / 29k); ≈ 100–255 h (mid ≈ 180 h; the MCSL lane ≈ 1–3 calendar weeks to finish the branch + 2–4 for the
queue, Weak in parallel).**  DONE recounted at the tip by the rev-53 diff method (plain `diff -ruN` against `~/dev/xv6iris` @ `802a9ab13`,
EVERY `Weak/Ax*.lean` excluded, NO git/jj; the unmerged branch NOT counted): **+131.1k gross / −8.5k removed / +122.5k net** (MachCSL
+25.3k, Xv6 +11.4k, Vtest +0.1k, Weak non-`Ax` +94.3k).  **% done by lines ≈ 131.1 ÷ (131.1 + 21) ≈ 86 % (range 82 % at 28.1k remaining …
91 % at 13.4k); net 122.5 ÷ (122.5 + 21) ≈ 85 %**; counting the after-capstone A1/A2/A4 (mid 11.5k) ≈ 80 %; counting the unmerged branch as
done would read ≈ 87 %.  Read with care: the remaining ≈ 14 % is ONE serial MachCSL lane (finish the branch — I3 and D17 are designs, not
started — then nine queue items) plus Weak work that cannot finish before it (P-W5/P-W6, P-W3r-h, 6e, 6j, 6n, 7); ≈ 2.7k (CertZ24–34) + ≈ 4–6k
of `Sil*` consumers are counted as done but superseded-but-green.

**[rev 56]**  Since rev 55: P-M1..P-M4 (MachCSL +5.3k/−1.9k incl. δ1's deletions), P-W2/P-W3/P-W4, `SbDevSt`/`SbHeadHop`/
`SbHeadHop2`, 6a (glue), 6b′ LANDED — ≈ +14.0k gross — while three things became VISIBLE: the [OWN.122] flip (+1.5–3k,
inside the P-M5–8 branch), the load-side residue of P-W3 (rows P-W3r-a..h, 3.1–6.4k; R46 §5: ≈ +1.5–3.3k net new over
what rows P-W3/P-W6/6m already carried) and the serial MCSL queue Q1–Q8 (2.7–6.3k; the records that retire the named
interim premises of 6a/6d/6j/P-W2/P-W4), and row 6d shrank under [OWN.115] (1.5–3k → 0.4–0.8k).  Under P now: P-M5–8
branch 5.3–9.8k + Q 2.7–6.3k (MCSL) + P-W5/P-W6 2.4–4.3k + P-W3r 3.1–6.4k (Weak) = **13.5–26.8k**; the rest 6c 0.8–1.5,
6d 0.4–0.8, 6e 0.8–1.5, 6g 0.3–0.8, 6h 0.5–1.2, 6j 0.8–1.6, 6m 0.3–0.8, 6n 1–2.5, 7 0.4–0.8, 8 0.1–0.2 = 5.4–11.7k.
**Σ remaining ≈ 18.9–38.5k (mid ≈ 29k; rev 55: 21.2–40.8k / 31k); ≈ 135–340 h (mid ≈ 235 h; the MCSL lane ≈ 3–6 calendar
weeks for the branch + 2–4 for the queue, Weak in parallel).**  DONE recounted at the tip by the rev-53 diff method (plain
`diff -ruN` against `~/dev/xv6iris` @ `802a9ab13`; NO git/jj) with EVERY `Weak/Ax*.lean` excluded — the baseline holds 367
and the weak tree 413 `Ax*` files (46 new + 126 modified) and they belong to the parallel AxSpin effort; rev 55 kept seven
of them (≈ 14k), so its +128.1k is NOT on this basis: **+128.2k gross / −8.5k removed / +119.6k net** (MachCSL +25.3k,
Xv6 +11.4k, Vtest +0.1k, Weak non-`Ax` +91.4k; 276 new non-`Ax` files 110.4k).  **% done by lines ≈ 128.2 ÷ (128.2 + 29)
≈ 82 % (range 77 % at 38.5k remaining … 87 % at 18.9k); net 119.6 ÷ (119.6 + 29) ≈ 81 %**; counting the after-capstone
A1/A2/A4 (mid 11.5k) ≈ 76 %.  Read with care: the remaining ≈ 18 % is ONE serial MachCSL lane (the red branch, then eight
queue items) plus Weak work that cannot finish before it (P-W5/P-W6, P-W3r-g/h, 6j, 6n, 7); ≈ 2.7k (CertZ24–34) + ≈ 4–6k of
`Sil*` consumers are counted as done but superseded-but-green.

*Rev 55's text (the record).*  Since rev 54: rows 1 (narrow δ1, closed at inc 16b; inc 19 superseded by P), 5 (X1), 5′ (E4) MERGED; 6l's
option-independent core (`SilOrd2`) and 6m's static half (`SilSiteTab`/`SilSiteTaint`/`SilSite`/`SilSiteStep`) landed
and are now mostly superseded by P (the pattern and the two-site rules are reused).  Under P: rows 6l, 6m's order half,
6b's twin half, 6f, 6j's E1 are ABSORBED by P-W3/P-W2/P-W6/P-W4; 6m shrinks to the lockstep-datum glue 0.3–0.8k; 6j =
E2–E4 + `lkFold` glue 0.8–1.6k; 6b′ 0.4–0.9k; unchanged 6a 1–2, 6c 0.8–1.5, 6d 1.5–3, 6e 0.8–1.5, 6g 0.3–0.8, 6h
0.5–1.2; 6n 1–2.5; 7 0.4–0.8; 8 0.1–0.2 — the rest ≈ 7.9–16.8k.
**Σ remaining ≈ 21.2–40.8k (mid ≈ 31k) — P 13.3–24.0k + the rest 7.9–16.8k; ≈ 150–350 h (mid ≈ 250 h; the MCSL
lane ≈ 3–6 calendar weeks serial, Weak in parallel).**  DONE (recounted by the rev-53 diff method at the tip before
P-W1's merge, 2026-10-19: **+127.1k gross / +118.2k net**, 261 new files 99.7k; + P-W1's 1,021 l.) ≈ **+128.1k gross /
+119.2k net**.  % done by lines ≈ 128.1 ÷ (128.1 + 31) ≈ **80 %** (range 76 % at 40.8k … 86 % at 21.2k); net 119.2 ÷
(119.2 + 31) ≈ 79 %.  By files: the MCSL lane touches 27 MachCSL files that break + 16 whose position comparisons
shift (P0(c)) and 16 Xv6 files (87 lines) + the mechanical rebuild of the 219 store-rule users; Weak adds ≈ 10–14
leaves.  Read with care: the remaining ≈ 20 % is dominated by ONE serial lane with two M− increments (P-M2's full
`interp_land`, P-M6's lock rules); ≈ 2.7k (CertZ24–34) + ≈ 4–6k of `Sil*` consumers are counted as done but
superseded-but-green.

## 8. Owner questions — ALL RULED (owner format kept as the record; [R45.8] informational items at the end)

**[rev 58]** The rulings of 2026-10-21, [OWN.137]–[OWN.150] (recorded, tightened, in the plan's §D rev 58 block; the ruling ledger `~/dev/weak-orch/allocproc_revise3_extra.txt`):
**[OWN.137]** `fetchReplayOk`'s early half NAMED until A2 + REVISIT 3 (landed `G7FetchOwn.fetchEarlyForeign :53`); **[OWN.138]** (r1) own-hart arm (landed); **[OWN.139]** Q-6H-3 (t3)
FAITHFUL, ~2–4k, after P-W6 (plan row A5 — after-capstone per the coordinator, inside per A7: flagged); **[OWN.140]** route P first, G-pv deferred, + the SPEC AUDIT; **[OWN.141]**
dependency tracking deferred to a graph machine; **[OWN.142]** Q-AUDIT-1 (a) keep (R1), SAIL-GAP-1 recorded, revisit after the capstone (A8); **[OWN.143]** Q-AUDIT-2 (ii) align `fence.i`
now — F1 landed, the no-drain half stopped by F-143-1; **[OWN.144]** Q-Q1-FETCH (E2) — landed as Q1-c; **[OWN.145]** Q-Q1-SPIN (s-a) — the "interrupts off" ghost record, with Q9;
**[OWN.146]** F-143-1 (c) — the drain KEPT, documented STRONGER (EX-FENCEI-1), M-S2 after the capstone (A7); **[OWN.147]** F-PW6-1/2 — REOPEN the route, P-W6 paused; **[OWN.148]**
F-PW6-2 (a) — the device-row drain gate, 0.4–0.9k, in `SbOrd`; **[OWN.149]** Q-A7-1 (a) **R-H** — conformance matrix → P-W6 with `IssueCo` + census + the gate; R-PF′ first after the
capstone (A6); K6; **[OWN.150]** Q-A7-2 (i) — the S-R `DomAt` lift NOW, kill > 3k.  The two A7 menus (Q-A7-1: (a) R-H [rec] | (b) R-PF′ now | (c) R-G now | (d) R-P unchanged; Q-A7-2:
(i) `DomAt` now [rec] | (ii) Q5–Q7 as planned | (iii) decide at rev 58) and their owner-format briefings are in `proposal-A7.md` §7.  **OPEN: NONE.**  The rev-57 paragraph follows.
**[rev 57]** The twelve rulings [OWN.125]–[OWN.136] (2026-10-20) were asked from the switch branch's findings F-11.1–F-11.6 and row 6e's
Q-6E-ARM, in the owner format inside `../xv6iris-weak-w1/PROGRESS-W11F.md` §11 and `~/dev/weak-orch/open_questions.txt`; they are
recorded, tightened, in the plan's §D (rev 57 block) and summarised in this note's header; §6 above carries the one that touches the
published statement's trusted surroundings ([OWN.131], the ONLY named xv6 assumption).  Supersessions: [OWN.128] WITHDRAWN (the owner had
answered only Q1 of a two-question menu); [OWN.130] → [OWN.134] (pipealloc SAFE, issue-stamp window, no assumption); [OWN.129] and
[OWN.133] → [OWN.135] (kvminit SAFE, premise dropped, the page-table conjuncts guarded by `started` landed).  Added 2026-10-21 from row 6h:
[OWN.137] (a) name `fetchReplayOk`'s early half until A2 + REVISIT, [OWN.138] (r1) own-hart arm.  **OPEN: NONE.**

### Q-R46-LOADSIDE — RULED [OWN.123] (2026-10-19 ~16:xx): (P) — NO load buffer, in the twin or in MachCSL

*Plain-language issue.*  RVWMO lets hardware reorder a hart's loads: a later load may be satisfied before an earlier one
(different addresses, nothing fencing them), and a later store may even become visible before an earlier load is
satisfied.  Any GENERAL machine model of RVWMO therefore needs a load-side mechanism besides the store buffer — the
owner's intuition ([OWN.120]/[OWN.121]).  Our proof does not run a general machine: it replays one known execution graph
of this kernel at a time on the buffered proof machine, step by step, and handles the reordered-load case by DELAYING
the competing store instead of reordering the load — the two loads run in program order and the "early" load still
sees the old value because the overwriting store has not been let through yet; same reads-from and coherence, only the
bookkeeping order differs, which the theorem does not speak of.  The trick fails only when the earlier load is itself
waiting for a store that has not arrived — an unlocked read — and xv6 has 18 such read instructions (+ 8 device reads),
each handled by a static argument (branch or fence next), by "never waiting", or by an exemption.  *Tiny example.*  Hart
z takes `L` (`amoswap.aq`) and writes its cpu pointer into `L->cpu`; the write sits in z's buffer.  Hart y, trying to take
`L`, runs `holding`: reads `L->locked` = 1 (z's swap), then `L->cpu` = the OLD value 0 — on hardware because the second
load was satisfied before z's write arrived; in the replay because z's write has not landed yet.  Same values, same
reads-from, loads in program order.  *Terms.*  *Load buffer*: a modelling device letting a later load be satisfied
before an earlier one.  *Store buffer / landing*: a store waits privately in its hart and LANDS later.  *Replay*: the
proof's step-by-step construction of a run of the proof machine from a graph.  *Blocked read*: one the replay cannot
take yet because the store it must return has not landed.  *Exempt read*: one the replay takes with a different value,
allowed when both values give the same branch.  *Options.*  **(P) no load buffer; the per-site fixes** — reads: "the
proof machine buffers stores exactly as RVWMO allows; loads run in order and read the latest value; every RVWMO
execution of this kernel is still covered because the proof delays the competing store instead of reordering the load,
and at three unlocked sanity reads it shows the value does not matter"; FAITHFUL (machine STRONGER only by forbidding a
reordering xv6 never exhibits); cost = the load-side residue ≈ 3.0–6.3k / 22–50 h in total, ≈ +1.5–3.3k / +10–25 h new.
**(P+L)** a load side in the twin only (early take, then re-sequence): FAITHFUL but the re-sequencing is the (R)
rescheduling rejected for δ1 [OWN.103]; +3–6k / 25–50 h, M−/L.  **(M+L)** out-of-order or promised loads in MachCSL:
machine closer to RVWMO, theorem unchanged in meaning; +10–25k / 80–200 h inside the red branch, L.  **Ruling: (P).**

### Q-R46-HH2 — RULED [OWN.124] (2026-10-19 ~16:xx): (a) exempt `holding+0x12` like `ip->ref` — WITH A REVISIT FLAG

*Plain-language issue.*  In `acquire`, xv6 first calls `holding(lk)` to detect a double acquire: it reads `lk->locked`
and, if 1, reads `lk->cpu` and compares it with `mycpu()`.  That second read is unlocked and may need a value another
hart has written but not yet landed; the replay then waits.  Nothing prevents the landing, but the progress
bookkeeping — a count that must strictly decrease at every wait — treats every upcoming store of the waiting hart as
something others might wait for, and RVWMO lets the hart's next stores (two pushes onto its own stack inside `mycpu`)
sit before the blocked read in the global order, so the count cannot be shown to decrease.  A proof artifact, not a
real stall.  *Tiny example.*  Hart z holds `L`, its `L->cpu = &cpus[z]` still buffered.  Hart x enters `acquire(L)`:
`holding` reads `L->locked` = 1, then must read `L->cpu`; the graph says it returns z's buffered pointer, so the replay
waits for z's write to land; meanwhile x's next instructions are `mycpu`'s `sd ra,8(sp)`, `sd s0,0(sp)` — private pushes
nobody else reads — and the global order may place them before x's blocked read.  *Terms.*  *Measure*: the decreasing
count.  *Waited-on event*: one the measure counts because some other wait could pass through it.  *Taint*: running the
hart with a register that differs between the two runs until the difference is dead (here at the `seqz` that makes the
compare 0 on both sides).  *Stack custody*: no hart touches another hart's live stack frame.  *Options.*  **(a) exempt
the read** as the two `ip->ref` reads are: the replay reads whatever is there (0 or another hart's pointer), the graph
reads z's pointer; both differ from x's own pointer, so `holding` returns 0 in both runs — "at three unlocked sanity
reads the replay may see a different value than the graph; the outcome of the check is the same"; FAITHFUL; 0.6–1.2k
Weak / 5–10 h; no new MachCSL record (the "a non-holder never reads its own pointer" fact is the export twin
`lkCpuReadAtP`); plus the shared `HoldZero` ([R46.3]).  **(b) refine the bookkeeping** so a store counts as waited-on
only when some hart could actually wait on it: "the progress argument knows private stack stores are nobody's
business"; FAITHFUL and general, but the clause about other harts' NEXT loads needs a new per-load MachCSL record on
the serial lane; 1.1–2.2k / 9–21 h.  **(c) assume progress** (name `noStuckP`): WEAKER; 0.  **Ruling: (a), "but this
should be somehow flagged as something to look at again" ⇒ REVISIT [OWN.124] in the Lean docstring, the plan's §D
REVISIT list (first item), the final theorem's documentation (`LinkDiscAdequacy`/`RvwmoXv6Adequacy` header) and every
status; (b) kept on file for a second site of this kind (none found).**

*Informational ([rev 56]; no menu).*  (v) **[OWN.122]** Q-P-M3-ORDER = (b): the MachCSL lane switches the machine on a
RED branch until P-M8 (the coordinator's provisional dual-then-flip (a) is overridden; F-P-M3-1 found the flip
inseparable from the readers).  (vi) **[OWN.116]** (R2″) — "an I/O access po-before a later RAM read is gmo-before it" —
is trusted platform text (STRONGER than RVWMO + PMAs, true of QEMU-TCG) used by H4; owner-ruled to be REMOVED with (R1)
in A4 (REVISIT list item 2).  (vii) **[OWN.117]–[OWN.120]** are MachCSL-lane / export decisions recorded in the plan (§D).

### Q-P-R1 — RULED [OWN.111] (2026-10-19 ~01:4x): route P RE-CONFIRMED over δ1′ after F-P1

*Plain-language issue.*  The hardware may delay a hart's store in a private buffer, including the store that
RELEASES a lock, so another hart can still see the lock as taken while the releaser has already taken a second lock
(F44-1).  P (a store buffer in the proof machine) was chosen partly because the K spike and census found a THREE-hart
instance in xv6 (console output through the UART) that the cheaper "δ1′" repair could not replay.  The published
theorem's header already carries a trusted platform assumption about memory-mapped I/O (`ioResidueGmo`, arm (R1))
that forbids exactly that instance, so the only known xv6 instance left was the TWO-hart one, which δ1′ replays
without a buffer.  *Tiny example.*  Hart 2: `release(P2.lock)` [buffered], then writes a character to the UART
[MMIO].  Under RVWMO + PMAs the character may reach the UART before the release reaches memory; under (R1) it may not.
*Terms.*  *Trusted item*: an unproved premise of the published theorem (§B(11)).  *(R1)*: "a RAM access
program-ordered before an I/O access is globally ordered before it".  *δ1′*: MachCSL's acquire raises the view only to
the position of the value it read.  *Options.*  (a) keep P — FAITHFUL, independent of any census, 14.5–25.5k; (b)
re-open δ1′ — FAITHFUL for the shapes it covers, its completeness rests on the census AND on (R1) for the UART chain,
≈ 6–11k; (c) P after the P0(b) check.  **Ruling: (c) then (a) — P0(b) confirmed F-P1 (`SBAcqP.uIoNo`), the owner
re-confirmed P knowing δ1′ would rely on (R1) while P replays the chain without it ((R1) stays for its other jobs).**

### Q-P-WFENCE-REF — RULED [OWN.112] (2026-10-19 ~02:xx): (a) the two-site reader exception

*Plain-language issue.*  xv6 reads an inode's reference count without a lock in two places (`ilock`, `iunlock`),
only to panic if it is below 1.  The hardware may let such a read be satisfied AFTER a later read of the same hart
(two loads of different addresses with nothing ordering them).  The route-P replay waits for a store to "land"
before anyone reads it, and holds a store back while someone still has to read the OLD value; with that unlocked
count read in the middle, three harts can each wait for one another and the replay stops — although the real
machine just runs on.  *Tiny example.*  Hart A decrements `dp->ref` right after releasing `dp`'s sleeplock.  Hart B
reads the new count (`ilock`), then, inside its own lock attempt, sees the sleeplock's spinlock still as "taken" (the
old value).  Hart C saw the spinlock released, took it, and later reads the OLD count in `iunlock`.  All three orders
are legal RVWMO; the replay needs A's count store landed for B, B's lock read done before A's release lands, C's lock
read done after it, and C's count read done before A's count store lands — a circle.  *Terms.*  *Land*: the moment a
store leaves the hart's private buffer and becomes visible to all.  *Gate*: the replay's rule for when a step may be
taken.  *Value-insensitive read*: a read whose value only feeds a check both possible values pass (here "≥ 1").
*Taint*: the proof's way of running a hart whose register holds a different value until that register is dead.
*Options.*  **(a) Exempt the two reads from the gate** (they read whatever has landed — provably ≥ 1 on both sides —
and run tainted until the compare): "the proof replays every behaviour exactly, except that at these two sanity
checks the replay may see a slightly older count; both counts pass the check."  FAITHFUL.  Cost +0.4–0.8k inside
P-W2/P-W3.  (b) a named premise excluding such executions: WEAKER, and the excluded executions are reachable.  (c)
change xv6 to read the count under `itable.lock`: FAITHFUL but out of scope [OWN.4].  **Ruling: (a).**

### Q-P-FIFO — RULED [OWN.113] (2026-10-19 ~02:xx): (b) per-address + fence-epoch buffer; final confirmation after P0(c)

*Plain-language issue.*  [OWN.110] said the proof machine's store buffer is a FIFO: a hart's stores reach memory in
program order.  RVWMO itself is weaker: two stores of one hart to different addresses may reach memory in either
order unless a fence sits between them.  The FIFO is harmless for the theorem only if the replay never needs the
weaker order — P0(a) checked every store in the kernel (1,331 store sites) and found it harmless apart from the
`ip->ref` case above (which the FIFO does not cause and (a) fixes), on the strength of a census plus a small argument
about `acquire`'s text.  A buffer that orders stores only by address and by fences needs no such census.  *Tiny
example.*  Hart A: `lk->cpu = me` (inside `acquire`), then `ip->ref++` — two unfenced stores.  FIFO: the second may not
land before the first.  RVWMO: either may land first.  *Terms.*  *FIFO*: first issued, first landed.  *Fence epoch*:
the count of `fence rw,w`-like fences a hart has executed; stores from an earlier epoch land before stores from a
later one (rule 4).  *Same-address order*: two stores of one hart to overlapping bytes land in program order (rule
1).  *Options.*  (a) FIFO + the census: machine STRONGER than RVWMO on the store side, theorem FAITHFUL; cost WCrel
leaf 0.1–0.3k + `lk->cpu` reader lemma 0.2–0.4k + the (E1) case.  **(b) per-address + fence-epoch**: "the proof
machine's store side IS RVWMO's" — FAITHFUL on both counts; cost +0.3–0.6k MachCSL (epoch per pending store, the
landing guard, the release rule reads the fence), −0.3–0.7k Weak; neutral overall; one more case in the riskiest
interpretation lemma.  **Ruling: (b), with the final confirmation after P0(c) measures the epoch case (item (5));
(a) stays the fallback instance of the same `landOk` parameter.**

### Q-P-δ1 — RULED [OWN.114] (2026-10-19 ~02:xx): (c) retire narrow δ1's stale-silent-AMO arm inside P-M1

*Plain-language issue.*  [OWN.105] gave the proof machine a rule letting a failed lock attempt read an older value
and leave no trace.  With the store buffer that rule is never needed: the "older value" is simply the current one,
because the release has not landed yet.  The rule can stay (dead) or go; going costs nothing extra if it goes in
the same edit that adds the buffer, because that edit re-proves every theorem the rule touches anyway.  *Tiny
example.*  Hart 1 spins on lock `d` while hart 2's release of `d` sits in hart 2's buffer: with the buffer the swap
reads 1 at the top — an ordinary failed swap; δ1's rule would let it read 1 "from the past" instead.  *Terms.*  *Dead
rule*: a machine behaviour no proof uses.  *Strict audit*: re-proving every registered theorem with the assumption
checker unchanged.  *P-M1*: the first MachCSL increment of route P.  *Options.*  (a) keep it dead with a side
condition "no pending stores": FAITHFUL; cost +0.3–0.8k of re-proof inside the P lane (every stale lemma gains a
case — the first design's "≈ 0.1k" was wrong, [R45.5]).  (b) retire it after P (cleanup row 8): (a) + 0.3–0.6k + one
more strict audit.  **(c) retire it inside P-M1**: FAITHFUL; cost ≈ 0 (deletions in the same edit and audit); the
three δ1 changes stay in history.  **Ruling: (c).**  Consequences for registered roots: none beyond P's own; rulings
touched: [OWN.105] superseded by [OWN.110]/[OWN.114] for its purpose, [OWN.109] moot, [OWN.103]'s "keep δ1 in mind"
fallback is history (the P lane lives on a branch until P-M8, so nothing merged loses δ1 before P works).

*Informational ([R45.8]; no menu).*  (i) [OWN.108] ("pinned loads replayed STALE") is SUPERSEDED by P: the gate
holds back the overwriting landing and the member reads the landed top — the ruling's per-site view/value datum is
vacuous (except the two `ip->ref` pcs, [OWN.112]).  (ii) [OWN.111]'s premise holds: P replays the UART chain using
only the fabric arm (R3); dropping the hart-side (R1) later is a sized after-capstone item (A4, 1–2.5k), not a
blocker — (R2)/(R2′) remain trusted platform text.  (iii) Q-6M-PTE (a) stays (progress of PTE-read heads, 0.3–0.6k
inside P-W3); Q-6M-ORDER / Q-6M-HOLD / Q-6M-GFVAL / Q-6L-PIN are moot under P.  (iv) [OWN.106]'s principle (step by
step, no order premise) is kept by P; [OWN.107] (B) is unaffected (6j's E2–E4 remain; E1 moves to P-W6).

## 9. Suggestions adopted ([R45.s1]–[R45.s4]; [rev 56] [R46.s1]–[R46.s4])

* **[R46.s1]** a `decide +kernel` leaf "LB-freedom unused" (row P-W3r-d, 0.05–0.15k, w2): for each of the 18 census pcs
  the instruction path to its certified branch contains no store, except `holding+0x12` (own frames: `mv s1,a5; jal mycpu`
  → `sd ra`/`sd s0`) and `ismapped+0x10` (return path) — `holding0CtrlNext`, `main16FenceNext`, `vdiShape`, `ptePctrlAlu`
  exist; `ilock+0xe`/`iunlock+0x1c` (`blez` next) and the two exceptions added as explicit statements.  It documents §1
  row L6: MachCSL-P's only load-side strengthening (no LB) is never exercised by a GF of this binary.
* **[R46.s2]** §1: `HRead`'s stale-view freedom (`tv` never raised by a plain load) is RVWMO's rules 2–3 in view form, left
  unused by the replay (member loads at the landed top); it stays for the Xv6 proofs.
* **[R46.s3]** census notes (§3.4 table; plan row 8's docs): `procdump` has no call site in the image (DEAD TEXT; the only
  references to `0x80002412` in `Xv6/KernelImage.lean` are its own entry and `KernelSyms.procdump`; its contract is stated
  unsatisfiable, `SpecProcdump.lean:40-45`), so its unlocked `p->state` reads are unreachable; `forkret+0x18`'s `first`
  read (`0x800019c6`) is chained through fork's `release(&np->lock)` (the writer `0x800019d6` is po-before it); this image
  has no `panicked`/`pr.locking` (panic paths end in `unreachable`).  Note: `~/dev/xv6-riscv/kernel/kernel.asm` is a
  DIFFERENT build (`holding` at `0x80000b82`, a `panicking` global) — every instruction fact here is from
  `Xv6/KernelImage.lean`.
* **[R46.s4]** the 12 named inputs of §3.4 get ONE table in the plan (after REMAINING WORK: owner, size, status), so the
  status reports can tick them.

* **[R45.s1]** `Weak/LitmusSBAcq.lean:4` "A LEAF: nothing imports this file" is STALE — `Weak/LitmusSBAcqP.lean:64`
  imports it and `Weak.lean:802-803` imports both; `LitmusSBAcqP.lean:3` says the same of itself.  Docstring fix →
  the plan's row 8 checklist (and P-W1, which edits `LitmusSBAcqP` anyway).
* **[R45.s2]** F-R45-1 mechanized inside P-W1 — DONE (`LitmusSBAcqP` §5 `l4Cat` + `l4NoMemberP` + `l4MemberX`; the
  witness has THREE rows, not R45's "four"; `l4NoMemberP` is policy-independent, confirming F-R45-1's "no buffer-order
  edge used").
* **[R45.s3]** the plan's §B(11b) "(R1)/(R2) ISA-given at three xv6 sites" corrected (none in-tree under D48).
* **[R45.s4]** P0(a)'s census tooling (the scratch Python CFG pass, `notes/W10-P0a-wfence.md` §1) is committed under
  `tools/` ONLY if P0(c) sends the buffer back to the FIFO fallback (the WCrel leaf's generator); under [OWN.113] (b)
  the leaf is not needed — recorded as conditional in the plan's row 8.
