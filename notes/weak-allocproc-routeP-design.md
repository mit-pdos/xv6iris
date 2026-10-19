# Route P design — an RVWMO-faithful per-hart STORE BUFFER in MachCSL with a lockstep replay

Design advisor (one-off, advisory: no proofs, no builds, no git/jj), 2026-10-19.  Inputs: plan rev 54
(`notes/weak-allocproc-plan.md`), R44 PART 0 (§0.1–0.5, the (P) paragraph of §0.4), `Weak/LitmusSBAcq.lean`
(F44-1 machine-checked: `SBAcq.l1Cat :203`, `l1NoMember :611`, `l1MemberSrc :736`, `l2cNo :548`), the K spike
(`notes/W10-K-spike.md` §6) and the K0 census (`notes/W10-K0-census.md` §3), rulings [OWN.2] [OWN.105]–[OWN.110];
the tip read for this note: `MachCSL/Lang.lean`, `TsoMem.lean`, `Resources.lean`, `Wp.lean`, `WpLock.lean`,
`Lock.lean`, `Reserved.lean`, `WordHistDefs.lean`, `KptInv.lean`, `Xv6/AccessDiscipline.lean` (ELEVEN conjuncts
`:1106-1108`, `dynLockWinZAt :934`, `ksFrameAt :1027`), `Weak/WeakAxiomatic.lean`, `WeakMem.lean`, `SilCand.lean`,
`SilOrd2.lean`, `SilSite.lean`, `SilKillT.lean`, `CertZ24.lean`, `CapF1.lean`, `MachOfPf.lean`,
`GraphFabResidue.lean`, `LockFacts.lean`, `tools/ci/roots.txt`, `roots-weak.txt`.  Every size is an unverified
estimate (ranges); every spec mark is w.r.t. riscv.cat / RVWMO / Sail / Zifencei / PMAs.

## 0. Summary, and one finding that the owner must see first

**The design in one paragraph.**  MachCSL keeps its timestamped byte histories, views and reservations; a plain
RAM store no longer appends at its instruction.  It is ISSUED into the hart's FIFO (`MState.sb cpu`) and LANDS at
any later machine step (a new, always-enabled hart arm; the landing appends the store to the log at the then-top,
exactly as `MState.store` does today).  Own loads (explicit and page-walker) forward per byte from the FIFO; a
`fence` with pw and sr (`rw,rw`, `rw,r`, `w,rw`, `w,r`, `tso`), `fence.i`, an `.rl`/RCsc access and any exclusive
access to a buffered byte must wait for the drain; an `.aq` AMO does NOT drain and its write overtakes the FIFO.
The ghost memory the WP rules see is the MERGED history (own pending entries on top of the landed ones), keyed by
ISSUE stamps — so the store WP rules keep today's shape — and landing is ghost-invisible to clients: it only sets a
monotone side map `lp : stamp → Option Nat` (landing position), which views compare against.  On the Weak side the
twin candidate gets the same FIFO; the walk is [OWN.106]'s step-by-step order with ONE uniform gate — *no write may
become the member-latest at a byte while a GF reader of its co-predecessor is unrealized, and no read is replayed
before its GF source is landed* — which makes EVERY member read return GF's value by construction.  Lockstep holds
with no skips, no silent arm, no stale replay and no per-site value datum; the silent-AMO twin, CertZ24–34,
`SilSite*` premises and narrow δ1's stale arm are retired as consumers (kept green).  Progress (`noStuckP`) is the
riskiest Weak piece; the merged-history ghost (`interp_land`) the riskiest MachCSL piece.  Size ≈ **14.5–25.5k
(MachCSL 8.5–15k serial, Weak 6–10.5k), 95–235 h**, confidence M− (M on the machine, M− on `noStuckP`).

**FINDING F-P1 (changes the premise of [OWN.110]; owner question Q-P-R1 in §8).**  The UART 3-hart chain that
the K spike (§3, §6) and the K0 census (§3) present as the xv6-reachable instance of Litmus 2 is **excluded by the
header's own trusted I/O item**: `ioResidue` arm (R1) (`Weak/GraphFabResidue.lean`, "RAM access po-before an I/O
event" ⇒ `gmoLt`, part of `ioResidueGmo`, a premise of T-alloc-RVWMO) orders hart 2's `sleep_prepare` release store
`w‴` (RAM, `0x80000cfa`) before its THR store `X` (`LIo`, `0x80000988`) in gmo; the chain needs `X < … < r3 <fr w‴`,
a gmo cycle.  The 2-hart UART variant (census §3 end) dies the same way.  The census explicitly notes "`w‴ <gmo X`
is not required" — true of RVWMO + PMAs, false under (R1), which is STRONGER than RVWMO + PMAs and already trusted.
Consequences: (i) the only F44-1 shape known to be in the quantifier is **Litmus 1** (2 harts, nested locks; `wait`/
`exit`, `scheduler`/`sched`, `kfree` after a release, `wakeup`'s loop); (ii) K-spike §6's verdict "δ1′ is not
sufficient on its own: a 3-hart residue through the UART fabric remains" loses its residue — δ1′ (acquire floor =
rf-source position; `SBAcq.l1MemberSrc`) covers every 2-hart shape and, modulo the census's completeness, every
xv6 shape; (iii) P remains the only route that is robust to shapes the census did not find (it needs NO census for
value agreement).  I was asked to design P and have; the owner should re-confirm P against δ1′ with F-P1 in hand
(§8).  Nothing below depends on the answer except the launch of the MachCSL lane (§5).

## 1. Spec first — what RVWMO / riscv.cat / Sail require of the buffer

Terms.  *Issue*: the store's instruction executes (the hart-local effect: forwarding becomes possible).  *Land*: the
store enters the global store order (gets its timestamp; foreign harts can see it).  *FIFO*: a hart's pending stores
land in issue order.  *Drain*: a step that cannot proceed until the hart's FIFO (or the entries overlapping an
address) is empty.  *Forward*: an own load returns the hart's own latest pending byte.

| # | riscv.cat / spec rule | what the buffer does | mark |
|---|---|---|---|
| 1 | `[M];po-loc;[W]` (CoWW, CoRW) | same-hart same-address plain W→W: FIFO order; R→W: the write lands later than any view the read used; an exclusive/AMO/SC write (lands at the top at once) to a buffered byte: the exclusive READ first drains the overlapping entries (`sbOverlaps` guard) | FAITHFUL |
| 2–3 | `[R];po-loc-no-w;[R]`, `rsw`/`fri` coherence | per-byte coherence floors as today (`HRead.coh`); an own pending store intervening resets the floor at ISSUE (forwarding then returns the own byte, co-later than anything landed) | FAITHFUL |
| 4 | FENCE pred/succ | pw∧sr (`rw,rw` `rw,r` `w,rw` `w,r` `tso`, and `iorw,iorw` — Sail drops the i/o bits, FIOM = 0): DRAIN, then today's `fencePost` (floor past `ownPub`, now the landed own last store).  pw∧sw only (`rw,w`, `w,w`): NO drain — FIFO already keeps same-hart W→W; R→W is free in a single order (as today, `TsoMem.lean` header).  pr∧sr (`r,r`, `r,rw`): floor := rv, no drain.  `r,w`: no-op | FAITHFUL for the drain fences; **the FIFO itself is STRONGER than RVWMO as a machine** (it orders ALL same-hart plain stores: 2+2W and unfenced-writer MP are not machine behaviours — exactly the registered TSO machine's strength, R44's "a strict subset of RVWMO's orders"); FAITHFUL for the GF quantifier iff `noStuckP` holds (§3.4: every xv6 GF has a FIFO member) |
| 5 | `[AQ];po;[M]` | an `.aq` exclusive read: floor := top (landing top) as today; it does NOT drain, and the pair's write lands at once, overtaking the FIFO (the F44-1 freedom) | FAITHFUL (owner [OWN.110]) |
| 6 | `[M];po;[RL]` | an `.rl` exclusive access drains everything first (xv6 has no `.rl`: `LockFacts.amoCensus`) | FAITHFUL |
| 7 | `[RCsc];po;[RCsc]` | an `.aq` AMO after an `.aq` AMO: both writes land at once in order — free; an `.aq.rl` drains by rule 6 | FAITHFUL |
| 8 | LR/SC pairs, atomicity | LR = exclusive read (drains overlapping entries, reservation as today); SC lands at once; a LANDING is blocked while another hart reserves the footprint (`othersReserve`, moved from issue to landing) | FAITHFUL |
| 9–13 | addr/data/ctrl deps, pipeline | reader-side; the machine tracks no dependencies (more permissive than RVWMO as today, [OWN.109] KEEP); a dependent store lands after the read it depends on anyway | unchanged (machine more permissive; theorem unaffected) |
| load value | visible = gmo-before ∨ po-before; co-max | own pending entries are po-before and will land after everything landed, so they are co-max among the visible: FORWARD per byte; mixed sizes: byte `j` from the hart's latest pending entry covering it, else the history at the load's view (`readFwd`) | FAITHFUL (cat is per byte; N10 mixed-size caveat unchanged) |
| Zifencei | stores before `fence.i` visible to the hart's later fetches | `fence.i` DRAINS, then raises `itv` as today (the ifetch agent never forwards) | FAITHFUL |
| `sfence.vma` | orders prior PTE stores before later implicit walker reads of the same hart | no-op as today (Q7): the walker's reads are the hart's plain reads and FORWARD from the FIFO — cat's load value already forces a po-earlier own store to be read | FAITHFUL w.r.t. cat (the priv spec's weaker implicit-read story is not what the tree's model transcribes; unchanged from today) |
| A/D write-back (Svadu) | implicit exclusive pair | the walker's A/D update is an exclusive pair: same-address drain, write lands at once (`pteDiscAt` unchanged) | FAITHFUL |
| I/O (PMAs) | MMIO ordered against RAM only by `fence` i/o bits, deps, rule 5 | MMIO accesses are NOT buffered (`devRead`/`devWrite` at the event, as today) and do NOT drain the RAM FIFO: a buffered RAM store may land after a later MMIO store | FAITHFUL to RVWMO + PMAs; the trusted (R1) is stronger and makes this freedom unused by xv6 GFs (F-P1) |
| DMA | silent in RVWMO | the disk reads/writes at the landing top as today; xv6's `fence iorw,iorw` before every notify drains, so descriptors/data are landed when the device looks | unchanged (device-model items of §B(11) stay) |
| interrupts, traps, `sret`, `wfi`, context switch | not fences | no drain (the kernel's hand-offs go through releases) | FAITHFUL |
| power loss | — | pending stores are lost (single era [R2.2]; the disk's durable image holds only DMA'd data) | FAITHFUL |
| narrow δ1 (stale silent AMO, `MState.silentOk` `Lang.lean:446`) | — | kept as a rule (sound, re-audited); gains the side condition `σ.sb cpu = []` (its `wv` bound reads `ownPub`, which cannot see pending stores); UNUSED by P's replay (a failed acquire reads the top because the release has not landed) | sound; Q-P-δ1 (§8): retire later |

The buffer changes NOTHING about what RVWMO/riscv.cat/Sail say; the only machine-vs-spec difference it introduces is
the FIFO (row 4), which it shares with today's machine.

## 2. The MachCSL change (serial lane; the registered machine edited, statements unchanged, strict audits — the
[OWN.105] precedent)

### 2.1 State (`MachCSL/Lang.lean:97-131` `MState`, `TsoMem.lean`)

Design choice (the load-bearing one — "issue stamps as identities, landing positions as the order"):

* `log : List Agent` becomes the ISSUE log (`top` = issue top; a store's history entry `⟨top+1, h, v⟩` is pushed at
  ISSUE, exactly `MState.store`'s `mem`/`log`/`pcAt` updates `Lang.lean:205-208` — the entry's `t` is its ISSUE
  stamp, a stable identity; `pcAt` stays keyed by it, so `relProvAt` is untouched);
* NEW `lp : Nat → Option Nat` (landing position of stamp `t`; `none` = pending) and `ltop : Nat` (landing top);
  NEW `sb : CPU → List Nat` (the hart's pending stamps, oldest first; invariant: exactly the own stamps with
  `lp = none`);
* histories are kept in CO order: landed entries by `lp` descending, PENDING entries on top of them.  The issue
  step inserts the new entry at the top of each footprint byte's history.  For a byte that already holds ANOTHER
  hart's pending entry the issue step chooses the relative position nondeterministically (the machine must be
  total); for xv6 this never happens (`pendOne` §2.4), and every store WP rule knows it from its precondition;
* views `tv`, `itv`, `hr.rv`, `hr.coh` and `wv` are LANDING positions.  `HEnt.visible lp h tv e := (lp e.t).any
  (· ≤ tv) || e.tid = h`; `Hist.read lp h tv H := (H.find? (visible lp h tv)).map v` — unchanged shape, one more
  argument (co order IS the list order, so the first visible entry is the co-maximal visible one);
  `Hist.top` = the first LANDED entry; `histOk` = descending `t` among the whole list is DROPPED, replaced by
  `histOkP`: pending prefix (all `lp = none`, descending `t`, one author) then landed suffix descending in `lp`,
  every landed `t` present in `llog` at its `lp`, FIFO per author (`lp` monotone in `t` within an author);
* `ownPub h log` → `ownPubL`: the landing position of `h`'s last LANDED store (= its last store after a drain);
* `bootFacts`: `lp = fun _ => none`, `ltop = 0`, `sb = fun _ => []` (`Lang.lean:398-403`, `bootWitness :414`).

### 2.2 Rules (`evStep` `Lang.lean:525-575`, `blockedStep :581-589`, `hartStep :692-697`)

```lean
-- issue (plain RAM store): no reservation check, no landing
| .memWrite n _ req, plain, ramBytes: σ' = σ.issue cpu req.pa n w            -- push ⟨top+1, cpu, w⟩ at each byte's
                                                                              -- top, log ++ [cpu], pcAt, sb ++ [top+1],
                                                                              -- hr.resetCoh (rule 2), tv/wv untouched
-- land: a NEW arm of hartStep at ANY m (the hart stutters one of its pending stores into the order)
| hartStep: … ∨ (landOk σ cpu ∧ m' = m ∧ σ' = σ.land cpu)
  landOk σ cpu := ∃ t rest, σ.sb cpu = t :: rest ∧ ¬ othersReserve σ.resv cpu (footprint of t)
  MState.land σ cpu := { σ with lp := lp[t ↦ ltop+1], ltop := ltop+1, llog := llog ++ [t], sb := rest }   -- mem, log, pcAt UNCHANGED
-- plain load: forward, then the history at a view in [tv, top]
| plain read: ∃ tvn w, tv ≤ tvn ∧ tvn ≤ ltop ∧ cohOk ∧ σ.readFwd cpu tvn pa n w ∧ σ' = σ.afterLoad cpu pa n tvn
  readFwd: byte j := the hart's latest pending entry covering pa+j if any (sbByte), else Hist.read lp (hartAgent cpu) tvn
  (afterLoad's loadSrcs stamps a forwarded byte 0 — own-sourced, as today)
-- exclusive read (LR / AMO read half / walker A/D read): same-address drain first
| excl read: ¬ sbOverlaps (σ.sb cpu) pa n ∧ ¬ othersReserve … ∧ (topBytes at the landed top ∨ the δ1 stale arm)
  blockedStep gains: akExcl ∧ sbOverlaps (σ.sb cpu) pa n ∧ σ' = σ   (self-loop until the landings happen)
-- exclusive write (AMO write / SC / A/D write-back): lands at once as today (`MState.store … excl := true` plus lp := ltop+1)
| excl write with rl (akRel, NEW classifier): additionally σ.sb cpu = [] (rule 6), else blocked
-- fences
| .barrier b: (fenceDrains b ∨ fenceIfetch b) → σ.sb cpu = [] (else blocked, NEW blockedStep arm); σ' = σ.fence cpu b with pub := ownPubL
-- δ1: silentOk gains σ.sb cpu = []
-- devices: dmaView/storeDma read/append at the LANDING top (ltop); unchanged otherwise
```

Why the landing is a hart arm and not a thread: a separate `Expr.sb` thread would change `powerFork`, the pool
relation of W4 (thread indices `MachOfPf.lean` header), `riscvPowerAdequacy`'s `Reducible` conclusion and Vtest's
executor; the hart arm touches `hartStep`, the two lifting lemmas `wpHart_lift_obs`/`wpHart_lift` (`Wp.lean:190,308`)
and the four `wpLoop_restart*` (`:2775-2879`, a Löb self-loop exactly like the K multi-tick arm, `W10-K-spike.md`
§2 R-K1), nothing else — provided landing is GHOST-INVISIBLE (§2.3).  Reducibility: the arm is enabled whenever the
FIFO is non-empty and unreserved; a drain-blocked fence self-loops (`blockedStep`), so `Reducible` is unchanged.

### 2.3 The state interpretation (`Resources.lean:2101` `eraInterp`, `:2193` `powerInterp`, `Adequacy.lean`)

The one principle: **a landing changes no resource any client can hold.**  Clients hold `histBytes`/`wordCell`
frags of the MERGED history (`σ.mem` as defined in §2.1: pending entries on top with their issue stamps) — landing
does not touch `σ.mem`, so these frags are unchanged.  What landing changes is `lp`/`ltop`/`sb`, which live in the
interpretation only:

* `lpAuth lp` (a monotone map: `none → some p` once) with PERSISTENT frags `landedAt t p` (`t ⤳ p`), minted by the
  interpretation at the landing and handed out by the rules that LEARN them (below); `sbAuth cpu l` owned by the
  interpretation alone (no client frag: the hart's knowledge of its own FIFO is the list of own entries with no
  `landedAt` — a derived notion `pendingOf cpu H`);
* the view resources `hartViewsAt` (`:995`) keep their shape (landing positions);
* NEW invariant clauses: `histOkP` (co-ordered histories, FIFO per author), `pendOne` (§2.4), and **`ctxLanded`**:
  for every certified context token (f2-ctx, `Ctx.lean`/`CtxBox.lean`: per-author vector bound `Vb`, release stamp
  `t_rel`, author `A`): whenever `lp t_rel = some p`, every entry of author `X` with stamp `≤ Vb X` is landed at
  `< p`.  It holds because (i) A's own entries `≤ Vb A ≤ t_rel` land before `t_rel` (FIFO) and (ii) a foreign
  author's entries `≤ Vb X` were LANDED when A acquired them (A's acquire floor is a landing position above them),
  and A's `t_rel` lands above any position that was the top at A's issue;
* **`interp_land`** (the central lemma): `machInterp σ ⊢ |==> machInterp (σ.land cpu)` — the ghost update of
  `lpAuth`/`sbAuth`, `histOkP`/`pendOne`/`ctxLanded` preserved, `mmOk`/`rsvOk` (`Adequacy.lean:485,501`) preserved,
  the chain conjunct (`:1495`), the kpt conjunct (`:1649`), the reserved-region conjunct (`:1832`), the user-epoch
  conjunct (`:2096`) preserved — each of these is stated over `σ.mem` and positions; they must be restated with
  `lp` where they order (`entAsOf`/`wordAsOf`/`memGrow`/`memAbove` in `ChainDefs.lean` — 126 comparison sites —,
  `KptInv` 25, `Lock` 22, `UEpoch*` 17, `WordHist` 10, `Reserved` 7) and are then INVARIANT under landing by
  monotonicity of `lp`.  This lemma is the MachCSL spike's acceptance (§5).

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
`started`, `au`/`auT` words, PTE slots, mint/free pages) — the Xv6 call sites do not see it; (ii) no reservation
check at issue (one premise fewer).  `pcAt`/`relProvAt` (`wp_s_sw_auT_pc` `WpStoreOrd.lean:375`) unchanged.
**Key lemma shapes** (new, in `WpAtomic.lean`/`Resources.lean`, replacing `memModel_store_*`'s plain half):
```lean
memModel_issue : mmOkP σ → pendOneAt σ pa n cpu → ramBytes pa n →
  machInterp σ ∗ histBytes pa n dqs Hs ⊢ |==> machInterp (σ.issue cpu pa n w) ∗ histBytes pa n dqs (pushed Hs (σ.top+1) cpu w)
interp_land  : machInterp σ ⊢ |==> machInterp (σ.land cpu)                                     -- §2.3
landedAt_of_drain : after `fence` with pw∧sr (or fence.i / rl): ∀ t, authored cpu t → t ≤ σ.top → ∃ p ≤ tv', landedAt t p
```
**Plain loads** (`memModel_read_*`, `exists_read_top`, `readsAre`, `read_cases`/`heads_eq` in `WordHist.lean`): the
side condition "`e.t ≤ tv` ⇒ the head is read" becomes `visibleAt e tv := landedAt e.t p ∧ p ≤ tv ∨ e.tid = cpu`.
Xv6 proofs rarely state `e.t ≤ tv` themselves (11 `Xv6/` files compare `.t` against positions: `AccessDiscipline`,
`DiskAcc`, `DiskInvDefs`, `IcachePinwObl`, `IcacheInvRef`, `KptTextIdent`, `KptMapIdent`, `StartedInv`,
`TextPristine`, `UEpochClose`, `UEpochDeposit`); they get visibility from the CONTEXT layer: `kctxL`/`ownCtx` with a
bound, converted at hops by `memModel_chainHop` (`Lock.lean` header of `isLock :1636`).  Under P the hop conversion
yields `visibleAt` from `ctxLanded` + the acquire's floor; the bound stays an ISSUE-stamp vector bound (`Vb`, which
[OWN.38]'s per-author design already is).  So: the context/hop lemmas change (`Ctx`/`KCtx`/`CtxBox`/`CtxX`), the
load rules' statements change their visibility side condition, most Xv6 call sites do not.
**Locks** (`WpLock.lean` 3.9k, `Lock.lean` 2k, `LockPayIff`, `LockBornHook`, `Reserved.lkFold :85`, `lockWinAt :140`):
the lock word's `WordHist 4` is read as a co-ordered list — with pending-on-top it already IS (the holder's pending
release sits above every foreign AMO write that lands meanwhile, and stays above when it lands: §2.1), so `lkFold`'s
alternation `A R A R …` is the LIST alternation as today; what changes is `lockWinAt`/`lockHistOk`'s "as of position"
reading (`lp`), and the release rule (`wp_s_sw_zero_release_*` `:2235-3649`) which must (i) mint the `ctxLanded`
certificate for its payload's vector bound (the FIFO fact "my earlier stamps land before this one" is the
interpretation's), (ii) not assume the release is visible at issue — the lock protocol's "released" state is entered
at ISSUE (ghost) while the word's landed value is still 1; the ACQUIRE rule (`wp_s_amoswap_lock*` `:1217-1760`) reads
the landed top, so a foreign acquire can fail against a pending release — that is a new, legitimate failed-spin case
of the acquire's loop (the same `bnez` arm; no new state), and a successful acquire reads a LANDED release, from
whose `landedAt` the floor and the hop follow.  `lkCpu_read_not_mine :283` (the `lk->cpu` value clause) is unchanged in
shape: the holder's pending `lk->cpu = me` store is on top of the merged history and is a hart's own entry.
**Fences** (`wp_s_fence_r_rw*`, `_iorw_iorw*`, `_rw_w` `WpLock.lean:36`): `rw,w` unchanged; the draining ones gain
the `landedAt_of_drain` postcondition and a blocked arm (Löb, like `wpLoop_restartB`).
**AMOs / walker pairs** (`WpAtomic`, `UMemAmo*`, `UkfWalk`): the exclusive read's same-address drain precondition is
discharged from the hart's own knowledge of its FIFO (`pendingOf`) — for the lock word the holder never has a pending
store to it except its own release (which it issues last), for PTE slots the walker is the same hart as the writer
only inside `sfence`-bracketed code; the rules state the drain as a Löb-blocked arm.
**Devices / DMA** (`WpDev*`, `WpDevDma` leases `dmaWriteLease :46`, `dmaReadPin :75`): MMIO rules unchanged; the DMA
lease rules need "the leased bytes are landed" — true after the driver's `fence iorw,iorw` (`landedAt_of_drain`), a
new premise auto-discharged at xv6's call sites (the W-DMA0 pattern [OWN.34]).
**Boot / Vtest**: `bootFacts`, `BootRun`, `vtest-lean/Vtest/XState.lean` (mirror of `MState`) and `HartExec.lean`
(executor policy: land immediately after issue — keeps every existing Vtest trace).

### 2.5 The export (`Xv6/AccessDiscipline.lean:1106-1108`, eleven conjuncts, `Xv6.xv6DiscAdequacy_closed`)

The conjunct LIST is unchanged (append-only kept).  Sub-definitions that ORDER by position read `lp` instead of `t`
(`chainOkAt`'s load-side clause at view `tvn`; `lockWordDiscAt`/`lkCpuReadAt` windows; `dynLockWinZAt :934`'s
`(p, t]` and `entAsOf … p`; `ksFrameAt :1027`'s `s < e.t`; `uptDiscAt`/`utextDiscAt` "after `itv`"); `relProvAt`
(keyed by issue stamp) and `kptMapsExp`/`cpuStaticAt` are untouched.  Weak consumes the export through `rmem`
(`Weak/PfStepTsoMem.lean`), which W4-P restates (§3.6); `RvwmoXv6Adequacy.lean` picks conjuncts by position —
unchanged.  As with X1's `custAt` carve, the export's sub-definitions move while `tcb/expected.json`'s module set
moves once if a new MachCSL module is added (keep the new definitions inside `Lang.lean`/`TsoMem.lean` to avoid it).

### 2.6 What Xv6 proofs see of a buffered store — the answer to the brief's question

Yes, "own buffered store visible as owned memory to its hart" is exactly the merged-history ghost: the hart's own
pending entry is an ordinary history entry it authored (visible to it at every view, co-max for it), so every own
read-back, every `tailOk`/`histBytes` manipulation and every transfer of `a ↦ H` into an invariant keeps today's
text.  The price is paid in three places only: visibility of FOREIGN entries (landing certificates instead of
`t ≤ tv`), the hop conversion (`ctxLanded`), and the lock word's two readings.  The rules do NOT stay unchanged in
their proofs (every memModel lemma is re-proved), but their STATEMENTS at the Xv6 interface do, except the load
rules' visibility side condition and the drain fences' extra postcondition.

## 3. The Weak side

### 3.1 The twin candidate `SbCand` (replaces `SilCand` as the realization's candidate; primed twin, registered
`mstep`/M1/M2 untouched [OWN.97][OWN.100])

`Mstate` (`Weak/WeakAxiomatic.lean:107`) + `msSb : Nat → List Wmsg` (pending messages per agent, oldest first).
Steps: `MStepLoad` with per-byte forwarding from `msSb i` (a forwarded byte's `t` is a PENDING marker; the label's
`ts` carries it — the same `Lbl` alphabet); `issue` for `LStore` (push, no log append; `storePostRun`'s
position-dependent parts deferred); `land i` (ADMIN step, no label: `msLog ++ [m]`, the deferred view updates at the
landing position `|log|+1`); `MStepFence` with drain preconditions mirroring §2.2; `MStepRmw` as today (reads
`rmwLatest` at the landed log — a failed acquire against a pending release reads 1 at the top: no silent arm); `MStepIo`
unchanged.  Embedding: every registered run is an `SbCand` run with each store landed right after its issue
(`SbCand.execWfOfOld`, the `SilCand.execWfOfOld :122` shape).  Spec: FAITHFUL (the candidate-level twin of §2).

### 3.2 The walk and THE GATE ([OWN.106]: built step by step; no order premise, no acyclicity assumed)

State: `SbWalk.St` = `SilWalk.St` (`Weak/SilWalk.lean:27-36`) with `c : SbCand.CandS`, program states `pst`, fabric
`dv`; the dependency shadow `sh` (`SilDep`, needed only to bound the silent write) is DROPPED.  Enabledness of row
`x` at its next GF event `e`, and of a landing, at walk state `S` (member-latest `latestW S b`, realized set):
```lean
inductive SbOrd.enb (GF D fab) (S) (cnt) : Item → Prop
  | fab   : nextIsFabric GF S cnt x → enb (.ev x)                              -- fabric members in fabric order (R43)
  | rd    : gisR e → (∀ b, srcOf GF e b = some w → landedOrOwn S x w b) → enb (.ev x)
            -- every GF source LANDED in the member (or the row's own pending store: forwarding)
  | wr    : gisW e → (∀ b, coPred GF e b = some w0 → latestW S b = some w0 ∧ readersRealized GF S w0 b) → enb (.ev x)
            -- an AMO / exclusive write: its GF co-predecessor is member-latest and all its GF readers are realized
            -- (for an AMO this includes the rf gate: the source IS the co-predecessor; `srcLatest` of R44 §2 + the
            -- K-spike's "reverse divergence" fr-gate, item 5, made uniform)
  | plain : plainStore e ∨ lbInert e ∨ gisIo e → enb (.ev x)                   -- issue is always enabled
  | land  : σ.sb x = w :: _ → (∀ b, coPred GF w b = some w0 → latestW S b = some w0 ∧ readersRealized GF S w0 b) →
            noResv … → enb (.land x)
```
**Value agreement by construction (`SbAgree.valEq`).**  Invariant: at every walk state, for every byte, the member's
landed co order is a prefix of GF's co at that byte, and every realized read returned its GF source's bytes.  Proof
per arm: `rd` — the source is member-latest (landed by the gate and nothing co-later has landed: a co-later write's
landing/AMO waits for this reader by `wr`/`land`); own pending source — forwarding returns it (GF's load value says
the read returns the own po-earlier store or a co-later write; a co-later write cannot have landed before an own
pending store, so it is the own store); `wr`/`land` — the co prefix extends by GF's next write.  Hence the member's
labels are GF's up to re-indexing (`lblReidxW` with EQUAL values), the datum is the registered lockstep datum
(`CertZ9.lockstepStep` / `CertZ13.hartStepOfSite` with `csync`), `relT` lockstep everywhere, and `agreeW4`'s four
clauses (`CertZ24.lean:72-87`) hold with `nf = True` (no failed-acquire exceptions) — including FULL lock co
(`lockCoSP` for free: member co = GF co per byte; `SilOrd2`'s windowed reconstruction §1–2 becomes unnecessary).
[OWN.108] is subsumed: a pinned load is gated on "source landed" and replayed at the member's TOP, which equals the
stale GF value because the overwriting landing is held back; the per-site view/value datum of row 6m is vacuous.

### 3.3 Why the two shapes are lockstep (walk-throughs; §4 has the full tables)

Litmus 1: both releases ISSUE (pending), both acquires of `e`/`c` land at once, each hart's spin read of the other's
lock is enabled (source = the other hart's acquire write, member-latest because the release is pending) and reads 1,
each failed `amoswap` is enabled (its co-predecessor is that acquire write; its readers — the spin reads — are
realized) and appends 1, and the releases LAND only after the last GF reader of their co-predecessors (the last
stale spin iteration) is realized, right before the acquire that GF has reading them.  Cross-spin ([OWN.100],
CertZ23/CertZ35's block): the same with the roles symmetric.  No skip, no silent step, no stale view.

### 3.4 Progress — `noStuckP` (the riskiest Weak lemma)

Claim: while GF events remain, some item is enabled.  Waits-for edges: (E1) `land w` → `land w′` for `w′` FIFO-before
`w` (same hart); (E2) `land w`/`wr e` → `land w0` for the co-predecessor `w0` (foreign, pending); (E3) `land w`/`wr e`
→ a GF reader `r` of `w0` (unrealized); (E4) `rd r`/`wr r` → the row's earlier unrealized event `e <po r`; (E5)
`rd r` → `land s` for its foreign source `s`; (E6) a drain fence → `land` of every own pending store; fabric waits
(R43 §5 iii).  Measure: the gmo position of the GF event behind each item (a landing's = its store's).  Every edge
is gmo-BACKWARD except (E1) and (E4): (E2) co ⊆ gmo; (E3) `r <fr w` (`SBAcq.frLt`); (E5) rf ⊆ gmo; (E6) rule 4
(pw with the fence's successor bit, `SBAcq.fenceLt`) orders the pending store before the fence's next memory event.
(E4) is R44 §5's case analysis (rule 5 for an `.aq` read `e`, rule 4 for a fence, the per-site dependency hops for the
census's pinned reads, fabric for device events) — unchanged; the new case "`e` is a plain load gated on an unlanded
source" is a RACY read (a chained source is landed by the time the chain's acquire is realized), i.e. a census site
again.  **(E1) is the new risk**: `w′ <po w` both plain, unfenced between them, is NOT gmo-ordered (W→W reordering),
and a cycle `land w′ →E3 r →E4 e →E5 land w →E1 land w′` is cat-CONSISTENT in general (an unfenced writer A: `x; y`
and a reader B: `y`-new then `x`-old — MP with no writer fence; and 2+2W deadlocks (E1)+(E2) alone).  So `noStuckP`
needs an xv6 fact at GF level for (E1): **P-WFENCE** — *every plain store `y` whose value a FOREIGN row reads is
either (a) at a release/publication site (`sw zero` after `fence rw,w`, `started` after `fence rw,w`:
`LockFacts.relAdj`, `relFenceBits`, `main+0xac`; class `WCrel`, `WeakMem.lean:650-651` `wRelp`), so rule 4 orders
every FIFO-earlier store before it and (E1) is backward; or (b) a `lk->cpu` store inside `acquire`, whose
FIFO-earlier stores are the hart's own per-cpu words (`push_off`'s `noff`/`intena`), which no foreign row reads
(W9a `PerCpu` pins), so no (E3) edge leaves them.*  (a) is an image fact (`decide +kernel` over `textPcs`, the
`LockFacts` style); (b) needs the per-cpu pin for the two stores — both static; the GF-level step is rule 4.  The
2+2W deadlock needs two harts writing the same two words unfenced with crossed co — excluded by (a)/(b) likewise
(every foreign-observed same-byte write pair is release-chained).  Progress then follows by pigeonhole over rows +
pending counts with the measure.  **This is what the P spike must check first (§5): the census of foreign-readable
plain stores that are not WCrel** — the K0 census tooling (`W10-K0-census.md` §2 method) finds them; I expect only
the `lk->cpu` stores and `initlock`'s `sw zero` (read by no one before publication).

### 3.5 Reuse / retire table

| piece | under P |
|---|---|
| `SilCand`/`SilCandLit`/`SilMember`/`SilDep`/`SilReplay`'s silent arm, `SilWalk2`, `SilRegZero`'s twin ghost, `SilClose` untrimmed kills | RETIRED as consumers (dead, keep green, headers "superseded by P"); `SbCand` is a new leaf beside them |
| `SilWalk` (state/snoc/okSnoc), `SilReplay.progOk` (program states), `SilAgree` (member/agreement shape), `SilPf*`/`SilEpf` (pf bridge) | REUSED, re-parametrized on `SbCand` (no `sil` column, no dep shadow, + pending lists) |
| `SilOrd2` §5–6 (the step-by-step gate `enb`, `prefW`/`prefG`, `walkPolG`, `recLogOfTr`, `cycleKillGZ`) | REUSED as the pattern; the gate's arms replaced by §3.2's (`silent`/`pin` arms gone, `land` arm added); §1–2 (windowed co reconstruction) UNNECESSARY (co agreement is total) — keep for the record |
| `SilSite` premises (`ordQ`/`silentQ`/`rmwQ`/`valQ`/`noPanicQ`/`custQ`/`drfQ`), `SilSiteStep`, the dynamic use of `SilSiteTaint` | RETIRED (values agree by construction); `SilSiteTab`/`SilSiteTaint` kept as the static census record; Q-6M-GFVAL, Q-6M-PTE, Q-6M-HOLD moot |
| `SilKillT.cycleKillCore :98` (twin-typed) → `cycleKillCZT` | REWRITTEN once for `SbCand` (`cycleKillCoreP`), same consumers (`CapFetchProv.t2linSupplyCZTtagged`) |
| `CapFetchProv`, `CapPcLog`, CertZ2–23 lockstep/transport, `CertZ9/13` datum, `LockFacts*`, `GraphFetchN2.csChainedT` | REUSED unchanged |
| CertZ24–34 (padded/skip/lag), the K-only rows 1′/6o/6p of R44 | NOT needed (dead, green) |
| narrow δ1 inc 15–16b | UNUSED by the replay; stays in the machine with the extra side condition (Q-P-δ1) |
| `CapF1.recRealizedH :50` (registered realization) | kept for M2; the member needs `recRealizedP` on the buffered twin W4 (§3.6) |

### 3.6 W4: two pieces

(a) **The registered `machRunOfPfRun` (`MachOfPf.lean:2958`) must be RE-PROVED** against the new `evStep` (serial,
right after the MachCSL change): a pf `LStore` row = MachCSL issue step + land step (`MRun` has no per-step thread
constraint); the simulation invariant adds "every FIFO is empty at every related state", so drain preconditions are
trivial, `rmem`'s `R-hist` becomes "merged history with every entry landed, `lp t = some t`" (issue and landing
coincide), `viewRel`/`TsoShadow` positions unchanged.  0.8–1.5k, mechanical.  M1/M2 (`roots-weak.txt`) re-registered
by re-proof, statements unchanged.
(b) **The buffered twin W4-P**: `SbCand` member runs (with pending lists) → MachCSL-P runs: `rmemP` = `rmem` +
`R-sb` (pending message lists ↔ `sb` stamps, with the merged histories' pending prefixes) + `R-lp` (pf log position
`k` ↔ `lp t = some (k+1)`); the land admin step ↔ the hart's land arm; loads at the member's top ↔ MachCSL loads at
`tvn = ltop` (always legal: `tv ≤ ltop`).  Its consumers: rows 6b (`segRealized`/`readAt` at the member) and 6j's E1
(the twin realization for `protReg` sourcing) — CapF6–CapF10's `readAt` parts re-derived at `recRealizedP`.  1.5–2.5k.

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

**The UART chain** (`W10-K0-census.md` §3; harts 2/1/3; `w‴` = `sleep_prepare`'s release of `P2.lock`, `X` = THR
store, `LSR₁` = `uartintr`'s LSR read, `R_y` = `release(cons)`, `A_y3` = the next `consoleintr`'s acquire, `r3` =
`holding+0x0` on `P2.lock`).  As §0 says, (R1) of `ioResidueGmo` makes this GF inconsistent, so the walk never meets
it; if (R1) were absent P replays it lockstep as follows: `I(w‴)` pending; `X` (MMIO, immediate, fabric order);
hart 1: `LSR₁` (fabric member, after `X`), `consoleintr`'s acquire/release of `cons` (`I(R_y)`; `L(R_y)` lands once
hart 3's/others' readers of `R_y`'s co-pred are realized — hart 3's `A_y3` reads `R_y` itself, not its co-pred, so
nothing holds `R_y` back except earlier spinners); hart 3: `A_y3` [`wr`: `R_y` landed ∧ latest], `wakeup`'s
`acquire(P2.lock)`: `r3` [`rd`: source = `P2`'s acquire write, latest because `w‴` is pending] R = 1 = GF, then the
long arm (`lk->cpu` read: source = `P2`'s pending-or-landed `lk->cpu` store — P2's `lk->cpu = &cpus[2]` was issued
before `w‴` and FIFO-lands before it; if still pending the read's source is "the previous value", also landed) and
failed swaps; finally `L(w‴)` after hart 3's last stale reader.  The MMIO store overtaking a buffered RAM store is
the one freedom P has that the registered machine lacks and K needed a skip for; under (R1) it is unused.

## 5. Increment plan

Lanes: **MCSL** = the serial MachCSL lane (one editor; δ1 is closed, X1 and E4 merged, so the lane is free);
**Weak** = parallel Weak-only slots.  Worker-hours at the observed rates (MachCSL cone 6–10 h/k, Weak leaves 4–8 h/k)
+ acceptance.  Acceptance gate for every MCSL increment: `lake build MachCSL Xv6 Weak Vtest` green, `audit.sh`
(+ `--weak --build`) with baseline/opaques unchanged, `tcb.sh` (module set moves at most once), statements of every
registered root textually unchanged (diff of `#print` signatures).

| # | increment | lane | lines | h | depends | conf. | acceptance |
|---|---|---|---|---|---|---|---|
| **P0** | **SPIKES (read-only / branch-only, before any launch)** — (a) P-WFENCE census: every plain store site of the image, with "foreign-readable?" and "WCrel (fence rw,w / rw,rw since the hart's previous store)?"; expected: only `lk->cpu` stores + `initlock` non-WCrel among foreign-readable; (b) Lean `decide` checks in a new `Weak/LitmusSBAcqP.lean` leaf: Litmus 1 HAS a P-member (a FIFO/landing `TsoCoreP` with the §3.2 gate, non-vacuity like `l1MemberSrc`); the UART chain is `ioResidue`-inconsistent (the F-P1 check); the unfenced-MP deadlock graph is cat-consistent (so the census is load-bearing); (c) the MachCSL representation on a scratch branch: `TsoMem`-P (`visible`/`read` with `lp`, `histOkP`), `MState.issue`/`land`, and the statement + proof of `interp_land` over a MINIMAL interpretation (`histBytes` + `lpAuth` + `sbAuth` + `histOkP`), plus `wp_s_sw` and `read_cases` re-proved — to measure churn and confirm ghost-invisibility | spike | 0.3–0.6k (b, c scratch) | 10–18 | — | H | report; (c) decides the P-M2 shape |
| P-M1 | `TsoMem`/`Lang`: state (`lp`, `ltop`, `llog`, `sb`), `visible`/`read`/`topBytes` with `lp`, `histOkP`, `issue`/`land`/`readFwd`/`sbOverlaps`, `evStep`/`blockedStep`/`hartStep` arms, `akRel`, `fenceDrains` drain, `bootFacts`; Vtest `XState` mirror | MCSL | 0.5–0.9k | 5–9 | P0 | M+ | builds; old `MState.store` kept for exclusive writes |
| P-M2 | interpretation: `lpAuth`/`landedAt`, `sbAuth`, `pendOne`, `ctxLanded`, `histOkP`; `interp_land`; `mmOk`/`rsvOk`/`memRam` lemmas; `Adequacy` | MCSL | 1.0–1.8k | 8–18 | P-M1 | M | `riscvPowerAdequacy` green, baseline unchanged |
| P-M3 | lifting: `wpHart_lift(_obs)`, `wpLoop_restart*` (Löb for land + drain-blocked arms), `memModel_issue/read/excl/fence` base lemmas (`WpAtomic`, `Resources`, `ReadAUr`), `WordHist` read lemmas with `visibleAt` | MCSL | 1.0–1.6k | 8–16 | P-M2 | M | `Wp`, `WpAtomic` green |
| P-M4 | the history layer: `WordHistDefs`/`WordHist`/`Reserved`/`ChainDefs`/`KptInv`/`UEpoch*`/`UIcache*` as-of/grow/visible lemmas over `lp`; the export's sub-definitions (§2.5) | MCSL | 2.0–3.5k | 15–35 | P-M3 | M− | `Xv6/AccessDiscipline` + `LinkDiscAdequacy` green; conjunct list unchanged |
| P-M5 | contexts/hops: `Ctx`/`KCtx`/`CtxBox`/`CtxX` (`memModel_chainHop` with `ctxLanded`; vector bounds unchanged) | MCSL | 0.8–1.5k | 6–15 | P-M4 | M | `CtxBox` green |
| P-M6 | locks: `Lock`/`WpLock`/`LockPayIff`/`LockBornHook`/`WpLockInit` (release rule mints `ctxLanded`; acquire reads the landed top; `lockWinAt`/`lkFold` readings) | MCSL | 1.5–2.5k | 10–25 | P-M5 | M− | `WpLock` green; `Xv6/Spin*`/`Sleeplock` green |
| P-M7 | store/fence/device rules: `WpSmodeRules`, `WpStoreOrd`, `WpStoreFree*`, `WpSmodeMint`, `WpSmodeAuRules`, `WpSmodeProc`, `WpSmodeFrame12b`, `WpSmodeFence*`, `WpSmodeDev*`, `WpDevDma` (lease landed premise), `UMemAmo*`/`UkfWalk` drain arms | MCSL | 0.8–1.4k | 6–14 | P-M6 | M | the 219 Xv6 call-site files rebuild with ≤ mechanical edits |
| P-M8 | the Xv6 fallout (11 position-comparing files + 22 `WordHist`-using files), `Boot`, Vtest `HartExec` policy, docs; full acceptance | MCSL | 0.9–1.8k | 8–18 | P-M7 | M | all roots re-proved, statements unchanged; `tcb.sh` |
| P-W1 | `SbCand` (candidate, run, embedding `execWfOfOld`), `LitmusSBAcqP` promoted | Weak | 0.5–0.9k | 3–7 | P0 | M+ | the two litmus members by `decide` |
| P-W2 | `SbWalk`/`SbReplay`/`SbAgree`: walk state, snoc, program states, `valEq` (values by construction), lockstep datum on `CertZ9/13` | Weak | 0.8–1.4k | 5–11 | P-W1 | M | `agreeW4` with `nf = True` derived |
| P-W3 | THE GATE + `noStuckP`: `SbOrd.enb`, the waits-for measure, the (E1) case from the P-WFENCE table (`decide +kernel`) + `PerCpu` pins + rule 4; `walkPolP`, `walkRunP` | Weak | 1.2–2.2k | 10–20 | P-W2, P0(a) | **M−** | `noStuckP` with NO named premise (fallback: NAMED, WEAKER, 0) |
| P-W4 | kill glue: `cycleKillCoreP` → `CatLin.cycleKillCZT`, `certSupplyP`, `acqAqP`/`relCoversP` at the member (`LockFacts2/3` reuse), `l2ClaimP` with `provAll` | Weak | 0.8–1.4k | 5–11 | P-W3 | M | `t2linSupplyCZTtagged` consumes it |
| P-W5 | registered W4 re-proof (issue+land, FIFO-empty invariant, `rmem`/`TsoShadow` with `lp`), M1/M2 re-registration | Weak (after P-M8) | 0.8–1.5k | 6–12 | P-M8 | M+ | `audit --weak --build` 13 roots green |
| P-W6 | buffered twin W4-P: `rmemP` (`R-sb`, `R-lp`), `simStepP`, `recRealizedP`; CapF6–10's `readAt` parts at the member (feeds 6b, 6j E1) | Weak | 1.5–2.5k | 10–20 | P-W5, P-W2 | M− | `segRealized`/`readAt` at `SbCand` members |
| **Σ P** | | | **14.5–25.5k** (MCSL 8.5–15k, Weak 6–10.5k) | **95–235** | | **M−** | |

Order: P0 now (one worker, ≤ 2 days) → P-M1..P-M8 serial in the MCSL lane (one editor; 3–5 rebuild cycles; the
long pole, ≈ 4–7 weeks of one slot) ∥ P-W1..P-W4 (independent of MachCSL until P-W5) ∥ the unaffected rows 6a/6c/
6d/6e/6f/6g/6h and 6b′.  P-W5/P-W6 after P-M8.  Riskiest step: **P-W3 `noStuckP`'s (E1) case** (a genuinely new
proof obligation: FIFO vs W→W freedom) and **P-M2 `interp_land`** (if the merged-history ghost is not
landing-invariant in some conjunct, the whole "store rules keep their shape" claim fails and the cost moves toward
R44's upper bound) — both are what P0 (a)–(c) measure first.

## 6. Published statement, trusted base, registered roots

* **T-alloc-RVWMO statement text (§A of the plan, `srvwmoXv6M2` + conclusion (b)): UNCHANGED.**  The quantifier is
  `rvwmoCatConsistentT ∧ ioResidueGmo ∧ xv6ConfS`; the conclusion speaks of "the realizing MachCSL run"; which machine
  realizes is proof content.  **Trusted base: UNCHANGED** — MachCSL is a proof device for T-alloc-RVWMO (confirmed:
  `MachCSL.*` appears nowhere in the published premises; it enters only through the registered MachCSL-tier roots
  the conclusion cites).  No new named premise; `noStuck` NAMED only as the fallback of P-W3 (WEAKER, [R44.7]).
* **The registered MachCSL-tier roots** (`tools/ci/roots.txt`: `MachCSL.riscvPowerAdequacy`,
  `Xv6.xv6FsAdequacy_closed`/`_xv6GF`, `userProof`, `unionAdequacyClosed`, `unionSyncCutNeg`, `unionResults`,
  `xv6NiAdequacy`/`TwoRun`/`TwoRunObs`/`StrongInstance`/`Out`/`Prefix`/`Det`, `xv6TextAdequacy_closed`,
  `xv6DiscAdequacy_closed`): statement TEXT unchanged, the MACHINE they quantify over changes (`primStep`'s arms) —
  the [OWN.105] precedent: every root re-proved, strict audit (`audit.sh`, `baseline.json` opaques expected
  unchanged: the two `resv` opaques, `bootImageSealed`, …), `tcb/expected.json` module set unchanged if no new module.
  For THESE roots MachCSL's memory model is the model being assumed, so their meaning moves from "TSO" to "RVWMO
  store side with a FIFO" — a documented strengthening of what the kernel proof covers.
* **Weak roots** (`roots-weak.txt`): M1/M2 (`srvwmoXv6M1Core`, `srvwmoXv6M1`, `srvwmoXv6M2`) re-proved via P-W5;
  the ten AxSpin roots import `MachCSL` (`Weak/AxSpinT2b.lean` etc. through `WeakMem`) but use neither `evStep` nor
  `TsoMem`'s read functions — expected unaffected; re-audited by `--weak --build` as a matter of course.
* `Xv6.xv6DiscAdequacy_closed`'s docstring/export sub-definitions move (§2.5); the conjunct list does not.

## 7. Σ remaining and % done (rev 54 baseline: Σ 17.7–36.9k, mid 27.3k; done ≈ 118.1k gross)

Since rev 54: rows 5 (X1, `ksFrameAt`) and 5′ (E4, `dynLockWinZAt`) MERGED (−1.4..−3.1k; landed lines not counted
here, ≈ +1.5–3k est.); row 1 closed at inc 16b (−2.8..−5.3k).  Under P: rows 6l, 6m's order half, 6b's twin half,
6j's E1 are ABSORBED by P-W3/P-W2/P-W6; 6m shrinks to the lockstep-datum glue 0.3–0.8k; 6j = E2–E4 + `lkFold`
glue 0.8–1.6k; 6b′ 0.4–0.9k; unchanged 6a 1–2, 6c 0.8–1.5, 6d 1.5–3, 6e 0.8–1.5, 6f 0.3–0.8, 6g 0.3–0.8, 6h 0.5–1.2;
6n 1–2.5; 7 0.4–0.8; 8 0.1–0.2.
**Σ remaining ≈ 22.7–43.1k (mid ≈ 33k) — P 14.5–25.5k + the rest 8.2–17.6k; ≈ 130–375 h (mid ≈ 250 h; the MCSL
lane ≈ 4–7 calendar weeks serial, Weak in parallel).**  % done by lines ≈ (118.1 + ≈2) ÷ (120 + 33) ≈ **78 %**
(range 74–84 %), down from 81 % because P makes ≈ 6k of new work visible while retiring ≈ 4k of planned twin/datum
work.  By files: the MCSL lane touches ≈ 45–60 of 293 MachCSL files and ≈ 30–40 of 2138 Xv6 files (mechanical for
most of the 219 store-rule users); Weak adds ≈ 10–14 leaves.  Read with care: the remaining 22 % is now dominated by
ONE serial lane with two M− items (`interp_land`, `noStuckP`).

## 8. Owner questions (owner format)

### Q-P-R1 — the 3-hart residue that motivated P is already excluded by a trusted item; confirm P over δ1′?

*Plain-language issue.*  The hardware may delay a hart's store in a private buffer, including the store that
RELEASES a lock, so another hart can still see the lock as taken while the releaser has already taken a second lock
(F44-1).  Three repair routes were on the table; P (a store buffer in the proof machine) was chosen partly because
the K spike and census found a THREE-hart instance in xv6 (console output through the UART) that the cheaper
"δ1′" repair could not replay.  Reading the header of the published theorem again: it already carries a trusted
platform assumption about memory-mapped I/O (`ioResidueGmo`, arm (R1): "whatever a hart did to RAM before touching
a device is visible before the device sees the touch").  That assumption forbids exactly the UART instance.  So the
only known xv6 instance left is the TWO-hart one, which δ1′ replays without a buffer.
*Tiny example.*  Hart 2: `release(P2.lock)` [buffered], then writes a character to the UART [MMIO].  Under RVWMO +
PMAs the character may reach the UART before the release reaches memory; under the header's (R1) it may not.  The
3-hart chain (hart 1 sees the character's effect, releases `cons`; hart 3 acquires `cons`, still sees `P2.lock`
held) needs the forbidden order.
*Terms.*  *Trusted item*: a premise of the published theorem that is not proved, listed in §B(11).  *(R1)*: the
arm "a RAM access program-ordered before an I/O access is globally ordered before it".  *δ1′*: MachCSL's acquire
raises the hart's view only to the position of the value it read, not to the top.  *P*: the store buffer of this
note.  *Census completeness*: whether every xv6 3-hart shape has been found.
*Options.*
**(a) Keep P (as ruled).**  An xv6 expert reads: "the proof machine has RVWMO's store side; every reachable
behaviour is replayed instruction for instruction, whatever shapes exist."  FAITHFUL.  Cost 14.5–25.5k / 95–235 h,
a 4–7-week serial MachCSL lane; retires the silent twin, skips, per-site value rules.  Independent of any census.
**(b) Re-open δ1′ now that the residue is gone.**  Reads: "the proof machine stays TSO-like; acquires are weakened to
what RVWMO's rule 5 gives; every two-hart shape is replayed stale."  FAITHFUL for the shapes it covers; its
completeness rests on the census (any 3-hart shape not going through I/O or lock words would break it — none is
known).  Cost ≈ 6–11k (K spike §6: floor change 0.8–2.5k MachCSL + twin floor + twin W4 2–3k + the 6m/6l datum
work that P retires), M−; keeps the silent twin and the per-site value datum.
**(c) P, but confirm F-P1 first by the P0(b) Lean check (half a day) before the MachCSL lane starts** — the
recommended procedure whichever option is taken.
Recommendation: (c), then the owner's call between (a) and (b); I lean (a) for robustness if the budget allows, (b)
if the 4–7-week serial lane is the constraint.

### Q-P-δ1 — keep or retire narrow δ1's stale silent AMO once P lands?

*Plain-language issue.*  The machine already has the "stale silent AMO" rule from [OWN.105] (a failed lock attempt
may read an old value and leave no trace).  Under P that rule is never needed (the old value is simply the current
one, because the release has not landed), and it needs one more side condition (no pending stores) to stay sound.
*Tiny example.*  Hart 1 spins on lock `d` while hart 2's release of `d` is still buffered: under P the swap reads 1
at the top — an ordinary failed swap; δ1's rule would let it read 1 "from the past" instead.
*Terms.*  *Silent AMO*: an atomic swap that writes back the value it read and appends no entry.  *Retire*: delete the
rule and re-prove the roots once more (strict audit).
*Options.*  **(a) Keep it (dead rule) with the side condition** — reads "the machine admits one more harmless
behaviour"; FAITHFUL; cost ≈ 0.1k inside P-M1, no separate audit.  **(b) Retire it in the cleanup row 8 after P** —
reads "the machine is the FIFO model, nothing else"; FAITHFUL; cost ≈ 0.3–0.6k + one strict audit.  Recommend (a)
now, (b) later.
