# Route P design — an RVWMO-faithful per-hart STORE BUFFER in MachCSL with a lockstep replay

Design advisor (one-off, advisory: no proofs, no builds, no git/jj), 2026-10-19.  **Revised 2026-10-19 (rev 55 of the
plan) by the reviser applying review R45 (`notes/weak-allocproc-plan-review-R45.md`; required changes [R45.1]–[R45.8],
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

## 0. Summary, and the two findings the owner has seen (F-P1 → [OWN.111]; F-R45-1 → [OWN.112])

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
replayed before its GF source is landed* — **with ONE exception ([OWN.112] (a), F-R45-1 §3.4): the two unlocked
`ip->ref` reads (`ilock+0xe`, `iunlock+0x1c`) are not gated; they read the landed top, provably ≥ 1 on both sides, and
run tainted until their `blez`** — which makes every other member read return GF's value by construction.  Lockstep
holds with no skips, no silent arm, no stale replay and no per-site value datum beyond those two pcs; the silent-AMO
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
98–222 h**, confidence M on the machine (P0(c) passed) and M on progress; **P-M1 is launchable now.**

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
| 4 | FENCE pred/succ | pw∧sr (`rw,rw` `rw,r` `w,rw` `w,r` `tso`, and `iorw,iorw` — Sail drops the i/o bits, FIOM = 0): DRAIN, then today's `fencePost` (`TsoMem.lean:491`; floor past `ownPub`, now the landed own last store).  pw∧sw only (`rw,w`, `w,w`): NO drain — it BUMPS the hart's fence epoch, so every entry issued before it lands before every entry issued after it; R→W is free in a single order (as today, `TsoMem.lean` header).  pr∧sr (`r,r`, `r,rw`): floor := rv, no drain.  `r,w`: no-op | FAITHFUL for the drain fences; **[OWN.113] the per-address + epoch buffer is FAITHFUL as a MACHINE too** (2+2W and unfenced-writer MP are machine behaviours, exactly RVWMO's store side); the FIFO fallback is STRONGER as a machine (it orders ALL same-hart plain stores), FAITHFUL for the GF quantifier iff `noStuckP`'s (E1) case is discharged (§3.4) |
| 5 | `[AQ];po;[M]` | an `.aq` exclusive read: floor := top (landing top) as today; it does NOT drain, and the pair's write lands at once, overtaking the buffer (the F44-1 freedom) — **F-P-W1-1 (P-W1, adopted): it may overtake ONLY the pending entries of the CURRENT fence epoch that do not touch its bytes.**  The first design let it overtake the WHOLE buffer, which violates rule 4: a `fence rw,w` orders every earlier store before every later WRITE, and the AMO's write is one (critical-section store → `release` → the next acquire's `amoswap` must not overtake the critical-section store).  So the exclusive write carries the SAME epoch guard as a landing (own entries of earlier epochs must be landed first — a blocked arm like the same-address drain); `SbCand` already has it | FAITHFUL (owner [OWN.110]; corrected by F-P-W1-1) |
| 6 | `[M];po;[RL]` | an `.rl` exclusive access drains everything first (xv6 has no `.rl`: `LockFacts.amoCensus :74`) | FAITHFUL |
| 7 | `[RCsc];po;[RCsc]` | an `.aq` AMO after an `.aq` AMO: both writes land at once in order (same epoch) — free; an `.aq.rl` drains by rule 6 | FAITHFUL |
| 8 | LR/SC pairs, atomicity | LR = exclusive read (drains overlapping entries, reservation as today); SC lands at once; a LANDING is blocked while another hart reserves the footprint (`othersReserve`, moved from issue to landing) | FAITHFUL |
| 9–13 | addr/data/ctrl deps, pipeline | reader-side; the machine tracks no dependencies (more permissive than RVWMO as today); a dependent store lands after the read it depends on anyway | unchanged (machine more permissive; theorem unaffected) |
| load value | visible = gmo-before ∨ po-before; co-max | own pending entries are po-before and will land after everything landed, so they are co-max among the visible: FORWARD per byte; mixed sizes: byte `j` from the hart's latest pending entry covering it, else the history at the load's view (`readFwd`) | FAITHFUL (cat is per byte; N10 mixed-size caveat unchanged) |
| Zifencei | stores before `fence.i` visible to the hart's later fetches | `fence.i` DRAINS, then raises `itv` as today (the ifetch agent never forwards).  **O-P-W1-a (P-W1):** the pf label `LFence false×4` names BOTH `fence.i` and the `sfence.vma` marker; `SbCand` does not drain on it (faithful to RVWMO, which has no fetch events), MachCSL drains at `fence.i`, and xv6 executes `fence.i` (`userret`) → the buffered twin W4-P (P-W6) needs a distinct fetch marker to relate the two (P-W6 item, +0.1–0.3k) | FAITHFUL |
| `sfence.vma` | orders prior PTE stores before later implicit walker reads of the same hart | no-op as today (Q7): the walker's reads are the hart's plain reads and FORWARD from the buffer — cat's load value already forces a po-earlier own store to be read | FAITHFUL w.r.t. cat (unchanged from today) |
| A/D write-back (Svadu) | implicit exclusive pair | the walker's A/D update is an exclusive pair: same-address drain, write lands at once (`pteDiscAt` unchanged) | FAITHFUL |
| I/O (PMAs) | MMIO ordered against RAM only by `fence` i/o bits, deps, rule 5 | MMIO accesses are NOT buffered (`devRead`/`devWrite` at the event, as today) and do NOT drain the RAM buffer: a buffered RAM store may land after a later MMIO store | FAITHFUL to RVWMO + PMAs (appendix (c1); Sail drops the i/o fence bits, D48); the trusted (R1) is stronger — P does NOT use it (§4, §6 A4) |
| DMA | silent in RVWMO | the disk reads/writes at the landing top as today; xv6's `fence iorw,iorw` before every notify drains, so descriptors/data are landed when the device looks | unchanged (device-model items of §B(11) stay) |
| interrupts, traps, `sret`, `wfi`, context switch | not fences | no drain (the kernel's hand-offs go through releases) | FAITHFUL |
| power loss | — | pending stores are lost (single era [R2.2]; the disk's durable image holds only DMA'd data) | FAITHFUL |
| narrow δ1 (stale silent AMO, `MState.silentOk` `Lang.lean:446`) | — | **RETIRED inside P-M1 ([OWN.114] (c), [R45.5])**: under P a failed acquire reads the LANDED top (the release has not landed ⇒ 1), so the stale arm is never used by the replay; the δ1 pieces are DELETED in the same edit and strict audit as the buffer (`xstale :123`, `afterExclStale :173`, `storeSilent :187`, `fenceWv :217`, `MState.fence`'s `wv` line `:236`, `staleFree :439`, `silentOk :446`, `staleBlocked :454`, the `not_silentOk_*`/`staleFree_*` lemmas `:458-480`, `blockedStep`'s stale arm, `WpLock`'s stale acquire outcome, `MachOfPf`'s and Vtest's stale cases; `MState.wv` goes with them).  Keeping it dead with `σ.sb cpu = []` would cost +0.3–0.8k of extra cases in every stale lemma P-M1..M8 re-proves (R45 A10), not 0.1k | FAITHFUL ((a)/(b) would keep one extra harmless behaviour) |

The buffer changes NOTHING about what RVWMO/riscv.cat/Sail say; with [OWN.113] the machine's store side IS RVWMO's.
The machine stays STRONGER than RVWMO only where it was already (the exclusive read's drain, row 1; no dependency
tracking is the opposite direction).

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
  precondition;
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
today's `t` is.  Two additions: (i) a side condition `pendOne`: the footprint holds no FOREIGN pending entry — read
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
/-- the two value-insensitive racy reads (`fs.c:300,325` `ip->ref < 1`; census 6m §3.3; P0(a) §5) -/
def ipRefPc (pc : Int) : Bool := pc = sym KernelSyms.«ilock» 0xe || pc = sym KernelSyms.«iunlock» 0x1c
def ipRefRd (GF : Gfexec) (e : Geid) : Prop := gisR e ∧ ipRefPc (pcOf GF e)      -- pc from the emission state

inductive SbOrd.enb (GF D fab) (S) (cnt) : Item → Prop
  | fab   : nextIsFabric GF S cnt x → enb (.ev x)                              -- fabric members in fabric order (R43)
  | rd    : gisR e → ¬ ipRefRd GF e → (∀ b, srcOf GF e b = some w → landedOrOwn S x w b) → enb (.ev x)
            -- every GF source LANDED in the member (or the row's own pending store: forwarding)
  | rdX   : ipRefRd GF e → enb (.ev x)      -- [OWN.112] no source gate; the member reads the landed top / own pending
  | wr    : gisW e → (∀ b, coPred GF e b = some w0 → latestW S b = some w0 ∧ readersRealized GF S w0 b) → enb (.ev x)
            -- an AMO / exclusive write: its GF co-predecessor is member-latest and all its GF readers are realized
            -- (for an AMO this includes the rf gate: the source IS the co-predecessor; `srcLatest` of R44 §2 + the
            -- K-spike's "reverse divergence" fr-gate, item 5, made uniform)
  | plain : plainStore e ∨ lbInert e ∨ gisIo e → enb (.ev x)                   -- issue is always enabled
  | land  : landablePol pol (σ.sb x) w → (∀ b, coPred GF w b = some w0 → latestW S b = some w0 ∧ readersRealized GF S w0 b) →
            noResv … → enb (.land x w)

/-- value agreement: exact everywhere except at the two pcs, where both words are in [1, 2^31) -/
def SbAgree.valEqX (GF) (S) : Prop :=
  ∀ r ∈ realized S, (¬ ipRefRd GF r → memberBytes S r = gfBytes GF r) ∧
                     (ipRefRd GF r → irefOk (memberWord S r) ∧ irefOk (gfWord GF r))
/-- the one value lemma, used on BOTH sides (GF co and the member's co-PREFIX of it): every write to `ip->ref`
    co-between the reader's own last `ref++` and any write the reader can see is an `itable.lock`-protected
    ±1 of a count that includes the reader's reference, hence ≥ 1 -/
theorem irefGe1 (GF) (B : row) (x : write of ref) : ownInc GF B ≤co x → x ≤co srcOf GF e_B → irefOk (val x)
/-- datum: the registered lockstep datum with TAINT at the two sites — LANDED as static rules already:
    `SilSiteTaint.ruIlock`/`ruIunlock :647-650` (the loaded `a5` feeds only the `blez` at `ilock+0x10` / `iunlock+0x1e`)
    and the value rule `SilSite.ruleOfIrefPos :207` (both values ≥ 1 ⇒ same arm); P-W2 re-hosts them on `SbCand` -/
theorem ipRefTailDies : ∀ pc, ipRefPc pc → loadTailDies pc {a5}
```
**Value agreement by construction (`SbAgree.valEqX`).**  Invariant: at every walk state, for every byte, the member's
landed co order is a prefix of GF's co at that byte, and every realized read other than the two pcs returned its GF
source's bytes.  Proof per arm: `rd` — the source is member-latest (landed by the gate and nothing co-later has
landed: a co-later write's landing/AMO waits for this reader by `wr`/`land`); own pending source — forwarding returns
it (GF's load value says the read returns the own po-earlier store or a co-later write; a co-later write cannot have
landed before an own pending store, so it is the own store); `wr`/`land` — the co prefix extends by GF's next write;
`rdX` — the member's landed writes to `ref` are a GF-co PREFIX, the reader's own `ref++` (`iget+0x58`/`idup+0x1c`,
program-before `e`) is landed or forwarded, and every landed write co-after it is in `irefGe1`'s interval, so the top
the member reads is ≥ 1 (`racyValOk :314` of the export says the same at the realized MachCSL state for an unchained
foreign entry; the GF lemma serves both sides).  Hence the member's labels are GF's up to re-indexing (`lblReidxW`
with EQUAL values except at the two pcs), the datum is the registered lockstep datum (`CertZ9.lockstepStep` /
`CertZ13.hartStepOfSite` with `csync`) with TAINT at the two pcs (`CertZ13.relT`, `CertZ11.loadTail`), `relT`
lockstep everywhere, and `agreeW4`'s four clauses (`CertZ24.lean:72-87`) hold with `nf = True` except at the two pcs —
including FULL lock co (`lockCoSP` for free: member co = GF co per byte; `SilOrd2`'s windowed reconstruction §1–2
becomes unnecessary).  [OWN.108] is SUPERSEDED ([R45.8]): a pinned load is gated on "source landed" and replayed at
the member's TOP, which equals the GF value because the overwriting landing is held back; no stale replay, and the
per-site view/value datum of row 6m is vacuous except for the two `ip->ref` pcs.
**Spec marks of the exception.**  (a) FAITHFUL (the GF is admitted; only the member's value at a value-insensitive
read differs, and the published statement speaks of GF's values through the kill, not the member's) — RULED
[OWN.112]; (b) a NAMED premise excluding these GFs would be WEAKER and false-ish (they are reachable xv6 behaviours);
(c) a kernel change (`ref` read under `itable.lock`) is out of scope [OWN.4].  Cost: `rdX` + `valEqX` + `irefGe1` +
re-hosting the two-site taint ≈ +0.4–0.8k on P-W2/P-W3 over the first design (of which `irefGe1` 0.2–0.4k was already
in row 6m's budget; the taint rules exist).

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
| H3 gated plain read with a pending foreign source = a RACY site (census 6m: `holding+0x0` (acquire path, pending release), `holding+0x12` (pending `lk->cpu`), `main+0x16` (`started`), `ip->ref` ×2, PTE ×9, `virtio_disk_intr` ×4, device `DRead` ×8) | `holding+0x0/+0x12`: `→ctrl amoswap.aq` (rule 11, the AMO is a write) `→(rule 5)` every later read — no read between (`li a0,0; ret; bnez; amoswap`); `started`: `fence r,rw` (rule 4); **`ip->ref`: FAILS (F-R45-1, below) → never a head by `rdX` [OWN.112]**; PTE: custody ⇒ source landed ⇒ never blocked (**Q-6M-PTE (a), NOT moot — [R45.3]**, 0.3–0.6k inside P-W3); `virtio_disk_intr`: sources are device stores (land at once) ⇒ never blocked; device `DRead`: fabric member (Efab) | static per site; one exception |
| H4 fabric member | (R3) | trusted arm |
| H5 drain-blocked exclusive read (walker A/D pair on an own pending PTE) | rule 1 to the pair's write; readers of the PTE's co-pred are custody-chained | custody (Q-6M-PTE (a)) |

Inputs of `noStuckP`: `rvwmoCatConsistentT`, `ioResidueGmo` ((R3) only), the image (H1/H3 `decide +kernel`),
`kernelAmoAq`, PTE custody at the realized prefix (6m F4 (a)); under the FIFO fallback additionally the WCrel census +
`lk->cpu` reader lemma.  NO named premise (fallback: NAMED, WEAKER, 0).  Confidence M (was M−): the obstruction is
understood and the table is finite.

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
| `SilSite` premises (`ordQ`/`silentQ`/`rmwQ`/`valQ`/`noPanicQ`/`custQ`/`drfQ`), `SilSiteStep`, the dynamic use of `SilSiteTaint` | RETIRED (values agree by construction, except the two pcs); `SilSiteTab`/`SilSiteTaint` kept as the static census record AND re-hosted for the two-site taint (`ruIlock`/`ruIunlock`), `SilSite.ruleOfIrefPos` likewise; Q-6M-GFVAL, Q-6M-HOLD, Q-6M-ORDER moot; **Q-6M-PTE (a) NOT moot ([R45.3]): PTE custody at the realized prefix is a P-W3 input (H3/H5)** |
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

## 5. Increment plan (rev 55: R45 §5 with the three rulings applied)

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
| P-M1 | `TsoMem`/`Lang` state + arms (§2.1–2.2: `lp`, `ltop`, `llog`, `sb` with epochs, `sbEp`, `landOk` = oldest epoch + footprint + no reservation, `issue`/`land`/`readFwd`/`sbOverlaps`, `insLanded` for exclusive/DMA writes, the AMO epoch guard (F-P-W1-1), `akRel`, drain/epoch fences, the silent land arm in `primStep`, `bootFacts`) **+ δ1 RETIREMENT ([OWN.114] (c): the deletions of §1's last row, same edit and audit)**; Vtest `XState` — **launchable NOW (P0(c) PASS, rulings in)** | MCSL | 0.6–1.1k | 5–11 | — | M+ | builds; `MState.store` kept for exclusive writes |
| P-M2 | interpretation: `lpAuth`/`landedAt`, `sbAuth`, `epochAt` + `landedBeforeOfEpoch`, `pendOne`, `ctxLanded`, `histOkP`; **the FULL `interp_land` EARLY, as the acceptance gate** (the landing-sensitive conjuncts: `mmOk`'s reservation clause, `curWordAt`/`uSlotNow` over the merged head, `dmaView`); `mmOk`/`rsvOk`; `Adequacy` | MCSL | 1.1–2.0k | 9–20 | P-M1 | M | `riscvPowerAdequacy` green |
| P-M3 | lifting + base memModel lemmas (`wpHart_lift_obsP` as spiked — per-event rules unchanged; `memModel_issue/read/excl/fence`; `WordHist` read lemmas with `visibleAt`; `memModel_store_plain*` callers → `memModel_issue`) | MCSL | 0.8–1.4k | 6–14 | P-M2 | M+ | `Wp`, `WpAtomic` green |
| P-M4 | history layer + export sub-definitions over `lp` (§2.5, incl. `dynLockWinZAt`'s window, `ksFrameAt`; the 319 position comparisons, ≈ 250 mechanical) | MCSL | 1.5–2.8k | 12–28 | P-M3 | M | `AccessDiscipline` + `LinkDiscAdequacy` green; conjunct list unchanged |
| P-M5 | contexts/hops (`Ctx`/`KCtx`/`CtxBox`/`CtxX`: `memModel_chainHop` with `ctxLanded`) **+ `pendOneOfCtx`** ([R45.4]) | MCSL | 0.9–1.6k | 7–16 | P-M4 | M | `CtxBox` green |
| P-M6 | locks: release rule STATES "my stores issued before the release fence land first" (from the `epochAt` token `wp_s_fence_rw_w` mints, consumed with "no own store since the fence", `relAdj`; FIFO fallback: from `sbAuth`), discharged at `release+0x16`/`main+0xac` ([R45.4]; +0.3–0.7k measured); acquire reads the landed top (+ the new failed-spin case; δ1 outcome deleted); the `insLanded` AMO postcondition on a word with a pending release; the AMO epoch guard discharged from `landedBeforeOfEpoch`; `lockWinAt`/`lkFold` readings | MCSL | 1.5–2.6k | 10–26 | P-M5 | M− | `WpLock`, `Xv6/Spin*`, `Sleeplock` green |
| P-M7 | store/fence/device rules (`WpSmodeRules`, `WpStoreOrd`, `WpStoreFree*`, `WpSmodeMint`, `WpSmodeAuRules`, `WpSmodeProc`, `WpSmodeFrame12b`, `WpSmodeFence*`, `WpSmodeDev*`, `WpDevDma` lease premise, `UMemAmo*`/`UkfWalk` drain arms) | MCSL | 0.8–1.4k | 6–14 | P-M6 | M | 219 call-site files rebuild with ≤ mechanical edits |
| P-M8 | Xv6 fallout (the 87 meaning-shifted lines in 16 files + the `WordHist`-using files), `Boot`, Vtest `HartExec` policy, docs, full acceptance | MCSL | 0.6–1.2k | 5–12 | P-M7 | M | all roots re-proved; `tcb.sh` |
| **P-W1** | ~~`SbCand` …~~ **DONE — MERGED** (`zsqxzoqp`: `Weak/SbCand.lean` 751 l. — `SbEnt`, `SbPol` four laws, `SbPol.epoch` primary / `SbPol.fifo` fallback / `SbPol.leEpoch`, `execWfP`, `execWfOfOld`; `Weak/SbCandLit.lean` 136 l. — `l1MemberSb` under every lawful policy; `LitmusSBAcqP` §5 (+134 l.) — `l4Cat`/`l4NoMemberP` (policy-independent)/`l4MemberX`; `Weak.lean:804-805`).  Findings: **F-P-W1-1** (the AMO's epoch guard, adopted), **O-P-W1-a** (`LFence false×4` = `fence.i` AND the `sfence.vma` marker → P-W6 fetch marker); forwarded-byte label timestamps → P-W2 | Weak | 0 (1,021 l. landed) | — | — | ✓ | |
| P-W2 | `SbWalk`/`SbReplay`/`SbAgree`: `valEqX`, the `rdX` arm, `irefGe1`, the two-site taint re-hosted (`ruIlock`/`ruIunlock`, `ruleOfIrefPos`), the forwarded-byte label timestamps, lockstep datum at `relT` (`CertZ9/13`) — **launchable now (w3)** | Weak | 1.0–1.8k | 6–14 | — | M | `agreeW4` with `nf = True` except the two pcs (tainted-lockstep) |
| P-W3 | THE GATE + **`noStuckP` per §3.4** (items/edges/µ, head table H1–H5, `kernelAmoAq`, PTE custody from 6m F4 (a) 0.3–0.6k); `walkPolP`, `walkRunP` — under (β) NO (E1) census case (FIFO fallback would add the WCrel leaf 0.1–0.3k + `lk->cpu` reader lemma 0.2–0.4k) | Weak | 1.3–2.4k | 10–22 | P-W2 | **M** | `noStuckP` with NO named premise (fallback: NAMED, WEAKER, 0) |
| P-W4 | kill glue: `cycleKillCoreP` → `CatLin.cycleKillCZT`, `certSupplyP`, `acqAqP`/`relCoversP` at the member (`LockFacts2/3` reuse — absorbs row 6f), `l2ClaimP` with `provAll` | Weak | 0.8–1.4k | 5–11 | P-W3 | M | `t2linSupplyCZTtagged` consumes it |
| P-W5 | registered W4 re-proof (buffer-empty invariant; stutter/fused arm per P0(c) (6)), M1/M2 re-registration | Weak (after P-M8) | 0.8–1.5k | 6–12 | P-M8 | M+ | `audit --weak --build` 13 roots green |
| P-W6 | buffered twin W4-P (`rmemP`: `R-sb` (+epochs), `R-lp`), `recRealizedP`; CapF6–10's `readAt` at the member (feeds 6b, 6j E1); **+ a distinct fetch marker for `fence.i` vs the `sfence.vma` marker (O-P-W1-a; `SbCand` does not drain on `LFence false×4`, MachCSL drains at `fence.i`, xv6's `userret` executes one)** | Weak | 1.6–2.8k | 11–22 | P-W5, P-W2 | M− | `segRealized`/`readAt` at `SbCand` members |
| **Σ P** | | | **13.3–24.0k** (MCSL 7.8–14.1k serial — P0(c)'s measure 6–10k for the churn proper + the epoch token, the merged-head restatement, Vtest and docs —, Weak 5.5–9.9k) | **98–222** | | **M** (machine M after P0(c); progress M) | |

Order: **P-M1 now** (the MCSL lane is free; P0(c) PASS, [OWN.112]–[OWN.114] RULED, [OWN.113] CONFIRMED) → P-M2 (the
full `interp_land` early = the gate) → … → P-M8 serial (≈ 3–6 calendar weeks of one slot) ∥ **P-W2 now** (w3) → P-W3
→ P-W4 ∥ the unaffected rows 6a/6c/6d/6e/6g/6h/6b′ (plan REMAINING WORK); P-W5/P-W6 after P-M8.  Row 6m under P =
`irefGe1` + the two-site taint (inside P-W2) + PTE custody (inside P-W3) + the lockstep-datum glue 0.3–0.8k; the
chain-based race-free-read theorem (6m F6) is retired (`valEqX` is it).  Riskiest steps now: **P-M2's full
`interp_land`** (the landing-sensitive conjuncts `curWordAt`/`uSlotNow`, `mmOk`'s reservation clause) and **P-M6**
(the release/`started` rules consuming the epoch token; the `insLanded` AMO postconditions) — both M−; `noStuckP` is M.

## 6. Published statement, trusted base, registered roots

* **T-alloc-RVWMO statement text (§A of the plan, `srvwmoXv6M2` + conclusion (b)): UNCHANGED.**  The quantifier is
  `rvwmoCatConsistentT ∧ ioResidueGmo ∧ xv6ConfS`; the conclusion speaks of "the realizing MachCSL run"; which machine
  realizes is proof content.  **Trusted base: UNCHANGED** — MachCSL is a proof device for T-alloc-RVWMO (confirmed:
  `MachCSL.*` appears nowhere in the published premises; it enters only through the registered MachCSL-tier roots
  the conclusion cites).  No new named premise; `noStuck` NAMED only as the fallback of P-W3 (WEAKER, [R44.7]).
  **[R45.7] Of `ioResidueGmo`'s arms the replay uses (R3) only (H4/Efab); (R1) is NOT used by P.**
* **The registered MachCSL-tier roots** (`tools/ci/roots.txt`: `MachCSL.riscvPowerAdequacy`,
  `Xv6.xv6FsAdequacy_closed`/`_xv6GF`, `userProof`, `unionAdequacyClosed`, `unionSyncCutNeg`, `unionResults`,
  `xv6NiAdequacy`/`TwoRun`/`TwoRunObs`/`StrongInstance`/`Out`/`Prefix`/`Det`, `xv6TextAdequacy_closed`,
  `xv6DiscAdequacy_closed`): statement TEXT unchanged, the MACHINE they quantify over changes (`primStep`'s arms) —
  the [OWN.105] precedent: every root re-proved, strict audit (`audit.sh`, `baseline.json` opaques expected
  unchanged: the two `resv` opaques, `bootImageSealed`, …), `tcb/expected.json` module set unchanged if no new module.
  For THESE roots MachCSL's memory model is the model being assumed, so their meaning moves from "TSO" to "RVWMO's
  store side" ([OWN.113]: exactly, up to the exclusive read's drain) — a documented strengthening of what the kernel
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

## 7. Σ remaining and % done (rev 55; see the plan's REMAINING WORK for the live table)

Since rev 54: rows 1 (narrow δ1, closed at inc 16b; inc 19 superseded by P), 5 (X1), 5′ (E4) MERGED; 6l's
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

## 9. Suggestions adopted ([R45.s1]–[R45.s4])

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
