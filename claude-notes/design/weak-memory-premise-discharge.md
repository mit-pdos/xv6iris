# Discharging `main_premises` — the analysis and the plan (phase 2)

**Status (2026-08-17): ANALYSIS + PLAN, written by the orchestrator after the
one-machine capstone closed
([`../projects/weak-memory-soundness.md`](../projects/weak-memory-soundness.md)).
Nothing here is built.  This is the last substantive premise of
`WeakEvCapstone.xv6_ev_weak_robust` besides the WP package; the earlier
notes called it "phase 2, exhibit-level discharge" without ever writing the
plan down.  Decision points for the user are marked ⚑.**

## 1. What the capstone still assumes, in plain language

`main_premises n_disk TS DS`, for every canonical traced bundle `(TS, DS)` of
every FULL-machine behavior of the image (`WeakRobustMain.v`):

| clause | says | why it is true of xv6 (informal) |
|---|---|---|
| `edges_split` | every cross-agent rf edge from a hart write `e1` (ts) to a hart read `e2` with a later fulfil is `edge_ok` — the reader is DISCIPLINED (aq read, or a `pr∧sw` fence between the read and its next fulfil) or COVERED (reader's `w_vwNew` ≥ ts already at the read) — or `bad` (the message is owned/`WCplain` and no publish by the author reaches `e2`) | lock words are read by aq-AMOs (disciplined); `started`/`first` are `lw; fence r,rw` (disciplined); every other cross-hart flow is lock/context-switch mediated: the reader's acquire raised its `w_vwNew` above the writer's release, which is above the writer's earlier stores (`covered` — MACHINE arithmetic once the release/acquire site facts are known) |
| `bad_wf` | if bad edges exist, some bad edge is minimal (no bad target strictly among its ancestors) | excludes thin-air ownership cycles; true because ownership only ever transfers through synchronization |
| `ee_ok` | for a floor-protection edge (`gE`: reader `r` of byte `a` with floor F, writer's later fulfil `y`), F < ts(y): FENCE-COVER (a `pw∧sw` fence po-between the writer's two events), WAW-COVER (writer's `w_vwNew` already ≥ F), or F = 0 | release sites fence before the flag store; ownership-transfer WAW is covered by the acquire |
| `dev_epoch_ok` | no rf/gE edge lowers the device epoch (no read of a promise across a device access) | the only cross-agent flows are the disciplined ones above; the disk's reads are aq-covered ring reads |
| `∃ sync, ptraces_bytes_ok` | every byte is single-writer, or written only by RMWs (`excl_byte` — lock words, PTE A/D), or HANDOFF (its writers are ordered through sync bytes) | lock words/PTE-A/D are RMW-only; everything else is written under a lock or by one hart at a time (context switch = handoff through the lock word) |

Two facts shape any discharge:

- **`bad` edges are ALREADY refuted** by `pf_violation_free_hart` inside
  `robust_main` (`bad_edge_violates`): a minimal bad edge replays to a pf run
  in which the read is a real read of an owned-unpublished message, i.e. a
  φ violation.  So `edges_split`'s remaining content is only about NON-owned
  messages (`WCrel`/`WCexcl`) and published owned ones.
- **The premises quantify over FULL-machine traces, whose program states
  after an EARLY read (of a promise) Iris never visits** (D-M6-8 in
  `completed/weak-memory-m6.md`).  So no φ-style state conjunct alone can
  discharge them; the archived design's split (a)/(b)/(c) still applies:
  (a) machine-side view arithmetic (provable per trace, premise-free);
  (b) VALUE-INDEPENDENT SITE facts (the aq bit of the reading instruction,
  "a `fence r,rw` is the instruction right after the racy load", "a
  `fence rw,w` is right before the release store"), which depend only on
  the pc at the event and which minimal-cycle structure makes pf-real,
  hence Iris/decoder-covered; (c) a static residue: discipline at positions
  po-after a pf-unsupported read, checkable per site on the image.

## 2. What is DIFFERENT now, and what it buys

1. **Every pf run is a language run** (`WeakEvCapstone` §2, at the same
   label).  The archived route needed a block-contiguous cone to make
   pf-real positions Iris-covered; now the cone is pf-real by construction
   and every pf-real event's program state is a `Sail gen c m fn` /
   `EDisk gen dp dws` expression the WP tree reasons about directly.  (b)'s
   "the pc at the event is Iris-covered" is therefore a statement about
   `weak_state_interp`/EWP at an event of the event language — no lift.
2. **The traced agents CARRY their program state** (`pexv6.PHart c m rs
   fn`): the pc is `register_lookup PC rs`, the instruction being executed
   is the residual monad `m`, and its access kinds are IN the monad node
   (that is how `pcls_ev` reads the class).  So the "site facts" of (b) are
   not facts about a pc looked up in the image; they are projections of the
   TRACED PROGRAM STATE — `disciplined`'s "aq read" is literally
   `ak_sync (classify (access_kind req)) = true` at the `MemRead` node the
   event stepped through, and "a fence follows before the next fulfil" is a
   fact about the SAME agent's later trace events (also recorded).  Only
   the question "WHICH instruction sequence is this" reduces to the image.
3. **The disk agent is now an ordinary agent** with a fixed program
   (`virtio_prog`): its discipline (aq read of `avail->idx`, `DFence`
   before `used->idx`) is DEFINITIONAL — provable once, for all traces,
   with no site enumeration.

## 2b. FINDING (2026-08-17, orchestrator): `edges_split` AS STATED IS FALSE FOR xv6 — the premise must be relativized to the fulfils the walk actually uses

`edges_split` demands, for a cross rf edge into reader `j`'s plain read at
`k`, that EVERY later fulfil `k'` of `j` be `edge_ok` (a `pr∧sw` fence
between `k` and `k'`, or `covered` AT THE READ `k`).  xv6's `acquire` is
`push_off(); if(holding(lk)) panic; while(amoswap.aq …); fence; lk->cpu = …`:
`holding` PLAINLY reads `lk->locked` (a foreign `WCexcl`/`WCrel` message —
not `bad`), and the reader's next fulfil is the acquire RMW itself with no
fence between and no coverage at the read (the reader has acquired nothing
yet).  So the edge is not `edge_ok`, and — worse — an early store po-after a
plain load to a different address is a LEGAL RVWMO reordering (LB shape), so
no per-edge inequality `ts < ts'` over ALL later fulfils can hold in every
behavior.  The behavior is HARMLESS: the walk (`WeakRobustAcyc2`) consumes
`rf_edges_ok` at ONE place (`mile_mu_gain`'s cross-rf arm) and only for a
reader ON A CYCLE, whose relevant later fulfil is the one the cycle leaves
through — i.e. a fulfil whose message is itself READ CROSS-AGENT (a
milestone source).  For xv6 those fulfils are: the acquire RMW (whose write
sits above the release it read: `ts < ts_rel < ts'`) and every CS store
(covered after the acquire).  Track A must therefore FIRST relativize the
premise (Track A0): weaken `edge_ok`/`edges_split` to exactly the
(reader, later-fulfil) pairs the walk needs — the later fulfil is a milestone
source, and coverage is evaluated at the FULFIL's EXT view (`fulfil_vpre`),
which for an RMW is after its own aq read — re-prove S1/the walk with it, and
only then discharge.  The weaker premise makes `robust_main` STRONGER (fewer
obligations), so it is a pure improvement of Layer 1.

## 3. The plan (three tracks, in order)

### Track A — the machine-side theory (Layer 1, generic, no xv6)
Prove, in a new `WeakRobustDisc.v` over an arbitrary bundle:
- **A1 `covered_of_handoff`**: if `e1` (writer `i`, ts) is po-before a
  `pw∧sw` fence of `i` which is po-before a store `s` of `i` (ts_s), and the
  reader `j` has an aq read of `s`'s message (or a read of it followed by a
  `pr∧sw` fence) po-before `e2`, then `covered T e2 ts` (EXT at `s` gives
  ts < ts_s; the acquire raises `w_vwNew j` ≥ ts_s; monotone thereafter).
  This is `edge_ok` for EVERY lock/flag-mediated edge, from site facts
  about the release site (`i`) and the acquire site (`j`) only.
- **A2 the transitive version**: chains of A1 hops (context switch through
  the scheduler lock, then the process lock…).
- **A3 `ee_ok` from the same site facts**: fence-cover for release sites;
  WAW-cover from A1's `w_vwNew` bound.
- **A4 `bytes_ok`**: `excl_byte` for bytes only ever written by `LRmw`;
  `handoff` for bytes whose writers are chained through A1 hops.
- **A5 `dev_epoch_ok`**: from A1 (an rf edge into a covered read has both
  ends' epochs ordered) plus the disk program's definitional discipline.
- **A6 `bad_wf`**: from `bad_min` of the FIRST bad target in… ⚑ open:
  needs a well-founded order on bad edges; candidate: the reader's fulfil
  timestamp.  Design in the track.
Every A-lemma is stated over TRACE FACTS: "event k of agent i is an aq read"
/ "is a `pw∧sw` fence" / "is a store of class WCrel" — all projections of
`aev`s and of `pa_st`.

### Track B — the site facts, from the traced program state
The A-lemmas' hypotheses are of the form "the reader's read event is aq"
(a fact about ONE event — value-independent, always available from the
event's own label: `LLoad true …`) and "a fence sits between k and k′" (a
fact about the SAME agent's later trace, also in `TS`).  What is NOT free is
the CLAIM that these fences/aq-bits are present at every relevant edge —
that is where the code discipline enters.  Two sub-routes, both needed:
- **B1 pf-real edges**: for edges whose reader position is pf-real (in the
  exhibit's cone), the reader's program state at the read IS an EWP-visible
  state; the racy-read leaf rules (`WeakRacy`, `WkStartedLoad`, the acquire
  leaves) can EXPORT a per-hart inert component ("read a WCrel/WCexcl
  message; no fence yet") into `weak_state_interp` — the D-M6-6 pattern
  (`w_relp`/`w_pub` are the precedent) — and adequacy exports "no hart
  fulfils while its flag is set" at every reachable state.  This is the
  reader-discipline export the M6 W3 list left unchecked; at event
  granularity it is a per-event rule obligation, which is exactly where the
  leaves already pay for the fence (`ewp_ev_started_fence`).
- **B2 non-pf-real positions** (po-after a pf-unsupported read): the
  static residue.  ⚑ DECISION NEEDED: carry it as an explicit
  per-site side condition on the image (a checker over the decode layer
  `KernelDecode*` enumerating the racy-read/release sites and verifying the
  fence adjacency), as D-M6-8 decided — OR strengthen B1's export so that
  the discipline flag is set by the READ EVENT ITSELF regardless of value
  (the aq bit and the fence adjacency are value-independent, so a
  pf-unsupported read at the same pc executes the same next instruction);
  the second needs the "minimal cycle ⇒ segment head pf-real" argument of
  D-M6-8 to be mechanized (`WeakRobustAcyc2`'s walk gives the cycle
  shape).  Recommendation: B1 first, measure what B2 must cover, then
  decide.

### Track C — the composition
State `main_premises` for xv6 as a THEOREM over canonical bundles from:
Track A lemmas + Track B exports + the disk program's definitional
discipline, and feed it to `xv6_ev_weak_robust`'s package hypothesis.

## 4. ⚑ Scope questions for the user (they change the theorem's fine print)

1. **User code.**  The behavior quantification covers arbitrary user
   programs on the disk image.  xv6 has no user-level shared memory, so
   cross-hart flows through user memory are context-switch mediated
   (Track A1/A2 cover them) — but this must be argued from the KERNEL's
   discipline (page ownership), and B2's static residue is about the
   kernel image only.  Is "arbitrary user code" in scope, or is the
   theorem stated for the fs image as shipped?
2. **The static residue.**  Accept a checker-emitted per-site side condition
   on the kernel image as a stated premise (auditable, D-M6-8's decision),
   or insist on the fully-mechanized B2 route?
3. **Ordering vs. the M4 port.**  Track B1's exports are per-leaf
   obligations — they belong INSIDE the M4 retarget (add the flag rule to
   the event-tier racy-read/fence rules as they are ported), so B1 should be
   designed BEFORE the port's chokepoint rules are re-proven, or those rules
   get re-touched.

## 5. Sizing (honest)

Track A: Layer-1 lemma work, generic, ~1–2 sessions of subagent proof time
with the orchestrator designing A1's exact statement (the crux).  Track B1:
one inert `wstate` component + rule obligations at ~4 leaf families +
adequacy export (three-line change) — a session, but it touches
`weak_state_interp`.  Track B2: unknown until B1 lands.  Track C: a day.
