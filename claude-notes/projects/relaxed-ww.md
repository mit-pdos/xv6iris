# Project: relaxing the memory model to allow store–store reordering (PSO)

**STATUS 2026-09-05: DESIGN ANALYSIS, not started.**  The companion of
[`relaxed-rr.md`](relaxed-rr.md) (load–load reordering), written to
answer: what does W→W reordering mean in the Ztso view machine, are the
two relaxations complementary, which order, which is easier to represent,
which costs more proof.  Measured against `main` at `434107f43`.

## 0. The answer in one paragraph

W→W reordering is the writer's freedom the way R→R is the reader's: in a
message-passing test either one produces the same "saw the flag, not the
data" outcome, and RVWMO allows both.  The two are orthogonal in the
machine and additive in what they admit; together (plus the total store
order and the R→W order this log keeps) they give RVWMO minus dependency
order minus load buffering.  But they are NOT symmetric in cost.  The TSO
port bought its whole ownership story from two facts about stores: a store
gets its timestamp AT ISSUE (so `ctx_pointsto` can carry the byte's
latest-write timestamp and `gen_heap` can be the flat log), and a hart's
view is a PREFIX of the log (so "clean = timestamp under the bound" is the
same as "visible on my hart").  R→R reordering keeps both facts and moves
one receipt.  W→W reordering necessarily breaks the second (a foreign
hart must be able to see my later store without my earlier one) and, in
its natural encoding, the first as well.  The least destructive encoding
keeps timestamps at issue and adds a global DRAINED set: a store is
visible to others only once drained, drains happen in any order at any
step, and a release-class fence (`w,w`, `rw,w`, `w,rw`, `rw,rw`, `w,r`,
`.rl`) drains all of the fencing hart's stores.  The proof price is that
every fact that moves a cell between harts — park/resume, deposit/withdraw
through the transit box, the lock rows, the racy-write ledger, the pins,
the DMA reads — must additionally carry "and it is drained", threaded
from the releaser's fence to the acquirer.  That is the layer R→R left
untouched.  Do R→R first; it is a fortnight and touches ~40 files.  W→W
is a redesign of the transport laws under the box's tripwires, plausibly
150–250 files and 6–10 agent-weeks, i.e. roughly half of the TSO port.

## 1. Why the current machine has W→W order, and what an observer needs

A store appends at issue: `log' = log ++ [PWMsg … h]`, timestamp
`S (length log)`, `gmem` updated in lock-step (`flat_store`).  So the log
order is program order per hart, every foreign hart's view is a prefix,
and a reader that sees my store at `t` sees every store of mine below
`t`.  To admit MP with a writer-side reordering, a reader must be able to
see my `y=1` and not my earlier `x=1`.  Two encodings:

**(A) Pending buffer, timestamp at drain.**  Stores enter a per-hart
pending list; an environment step moves one pending message to the log
(per-byte FIFO, otherwise any order), where it gets its timestamp.
Visibility stays a prefix, so every READ gate, floor and view law
survives verbatim.  The price is on the store side: a dirty cell has no
timestamp until it drains, `gmem = flat log` no longer holds the owner's
value, two harts' pending stores to one byte have no coherence order
until drained (so no "issue-flat" cache exists either), and the racy-write
ledger (`phys_ledger_rpay`, `rel_cells`, `TsRel`, `started_win_rel i`,
the lock word's release history) names log POSITIONS at the store, which
would not exist yet.  Client-owned fragments cannot be updated by a drain
step nobody executes, so `ctx_pointsto`'s dirty arm and the whole T3
write tier (`TsoCtxStore` 1431 lines, `TsoMemPa`'s `win_ok`/`racy_read_*`
theory ~2000 lines, `StartedInv`, `WpLock`'s `lock_word_ex`) would be
re-founded.  Rejected.

**(B) Reserved slots, timestamp at issue, a drained set.**  Recommended.
Stores append at issue exactly as today (timestamps, `gmem`, the TM tie,
every store gate, every ledger position: unchanged).  A global monotone
set `D` of drained slots is added; visibility becomes

    visible h tv t  :=  (t ≤ tv ∧ t ∈ D) ∨ author t = h

Own messages are always visible (forwarding, as today).  Coherence order
is issue order, so per-byte FIFO comes for free — a later same-byte store
draining first is harmless because `read_down` is latest-visible.
Drains are environment nondeterminism: every `prim_step` may grow `D`
arbitrarily (`∃ D' ⊇ D`), so a store becomes visible "eventually, at any
time" as on hardware.  A release-class fence forces `D := D ∪ {own slots}`
("all my prior stores have drained"); flush-at-fence and barrier-in-buffer
are observationally the same here because a fence is unobservable except
through the hart's later stores, which drain after it in either reading.

### 1.1 The arms under (B)

- **Plain load**: `tvn ≥ tv`, read latest-visible with the new
  `visible` (non-prefix: undrained foreign slots below `tvn` are skipped).
  Under TSO-with-W→W the load still sets `tv := tvn` (R→R kept); combined
  with relaxed-rr it does not.
- **Store**: unchanged append; the slot is born undrained (own-visible).
- **Exclusive read / AMO**: reads the latest-visible at the top — NOT the
  flat cache any more, because a foreign undrained store must not be seen
  (a pending release `sw locked=0` keeps the lock word at 1 for an
  `amoswap` until it drains).  `tso_read_top_flat`, the SC collapse the
  lock leaves lean on, holds only when every slot is drained.  The AMO's
  write appends and is drained immediately (an AMO is performed at
  memory); an `.rl` AMO first drains the hart's own slots.
- **Barrier**: `fence_drains` (W→R) keeps raising `tv` past `own_pub` AND
  now drains own slots; the release kinds `w,w`, `rw,w` drain own slots
  without touching `tv`; `fence.tso` drains; `r,*` kinds do nothing here
  (they are relaxed-rr's business).  So `fence rw,w`, a no-op under both
  Ztso and relaxed-rr, becomes THE load-bearing fence of the ownership
  layer.
- **DMA**: `disk_step` reads `g.(gmem)` today (the flat cache).  It must
  read latest-visible-drained at the top instead, or the device sees the
  driver's undrained descriptor stores; the `__sync_synchronize` before
  the MMIO notify is what drains them.

### 1.2 Litmus (TsoLitmus.v)

| test | Ztso | (B) | RVWMO |
|---|---|---|---|
| MP, no fences | forbidden | **allowed** (writer reorders) | allowed |
| MP + writer `fence w,w` only | forbidden | forbidden (reader R→R kept) | allowed |
| MP + writer `fence w,w` + reader `fence r,r` | forbidden | forbidden | forbidden |
| CoWW (same byte, one writer) | forbidden | forbidden (issue-order coherence) | forbidden |
| 2+2W | forbidden | **allowed** | allowed |
| S (store, store / load-of-second, store-to-first) | forbidden | **allowed** without writer fence | allowed |
| SB, SB+fence, n6, LB, IRIW, CoRR | as today | as today (IRIW: still forbidden — one log) | — |

## 2. What the ghost layer has to carry: drained-ness

### 2.1 The invariant that breaks

`own_context ξ` says: bound `B ≤ K ≤ tv_h` and every clean fact
(timestamp `≤ B`) is visible on the hart I run on.  Under (B) a clean
foreign-authored fact with `t ≤ tv_h` is visible only if `t ∈ D`.  So the
context invariant becomes **clean ⟹ drained; dirty ⟹ authored by this
hart** (drained or not — forwarding covers it).  Everything that turns
dirty facts into clean ones — `ctx_park` + `ctx_resume`, `ctx_deposit`,
`ctx_absorb_lb`, `ctx_dom_of_parked`, the box's withdraw/checkout floors —
must be justified by a DRAIN RECEIPT for the dirty entries' author.

### 2.2 The receipt and where it is born

Per hart a monotone `dw_h` ("all slots authored by `h` at or below `dw_h`
are drained"), raised to `own_pub h log` at every release-class fence; a
persistent receipt `drain_lb h N`.  The fence leaf (`HartBarrier.pub_step`,
today "the receipt is born at the leaf and nowhere else") is the one
minting point; `WpSconfFencePub` gets the release form at `fence rw,w`.
Between hart A's fence and hart B's acquire the receipt travels the way
floors travel today: in the lock's release row (R2, folded at the `_in`
release) and in the llb-tier acquire post (R1).

### 2.3 The parked forms

A record parked at swtch (`SwtchCtx`, the proc's saved context) is parked
BEFORE the scheduler's release fence, so it cannot be drained at park
time.  Two parked spellings are therefore forced: `ctx_parked_pend ξ T A`
(entries authored by hart `A`, drain pending) and today's `ctx_parked ξ T`
(drained), with `ctx_parked_drain : drain_lb A N → T ≤ N →
ctx_parked_pend ξ T A ==∗ ctx_parked ξ T`.  Who runs the upgrade is a
ruling: the RELEASER (after its fence, for everything it parked or
deposited under the lock — needs a `DrainMorph`-style class over every
payload shape, since the payload is in dep form at release), or the
ACQUIRER (which already takes floors at R1/R2 and would take the receipt
beside them — the parked record must then name its author).  The box's
stamps `(id, stamp)` would carry the author or the receipt would ride the
lock row; either is an eighth-transition-class change under
`ctx-box.md` §4's tripwires and needs the owner's ruling.  The FLOORS law
(`ctx_floor_dom`, `ctx_dom_wrote_floor`) gains a drained arm.

### 2.4 The racy tiers

- **Lock word** (`WpLock.lock_word_ex`, `WpSconfLock`, `ProofAcquire`,
  `ProofRelease`): the `amoswap.aq` may now read `locked = 1` while the
  ghost says released (the release store is undrained).  The protocol
  gains a "released, not yet drained" state; the AMO leaf's obligation
  changes from a `gen_heap` fact (`mem_bytes_at σ`) to a visibility fact.
- **`started`** (`StartedInv`, `ProofMainSecondary`): the release-armed
  window's history position is drained by hart 0's `fence rw,w` at
  `main+0xac` — today the generic no-op leaf, becomes the publishing
  release leaf; the reader's absorb takes the receipt.
- **Pins** (`pin_ok`, `KptPublish.kptree_publish_top`): "every view ≥ B
  reads a value in `Sv`" needs every write in the window drained; the
  KPT publication already sits at that fence, so the mint takes the
  receipt.  The pure theory in `TsoMemPa` (`pin_ok`, `win_ok`, `racy_read_*`,
  `own_last`, `writer_pin`, ~1500 lines) gets a `D` parameter.
- **DMA / virtio** (`VirtioProto` 8192 lines, `DiskAvail`, `DiskInv`,
  `ProofVirtioDiskRw*`, `ProofVirtioDiskIntr`): the device reads drained
  memory; the driver's descriptor and avail-ring stores are drained by the
  `fence` before the notify, and the protocol's "published" facts must
  say so.

## 3. The four questions

**Complementary?**  Yes.  R→R is a per-hart reader freedom (which view a
load reads at); W→W is a global writer freedom (when a slot becomes
visible).  They compose without interaction — the read arm takes both
changes side by side — and the combined machine is "RVWMO minus
syntactic dependencies, minus load buffering, with a total store order",
which is where a log-based model naturally stops.

**Order?**  R→R first.  It is self-contained (one receipt moves from the
load to the acquire fence), it builds the acquire-side fence leaf that
W→W's release-side leaf mirrors, and it validates the claim that the
ownership layer is view-agnostic before W→W goes and changes that layer.
Doing W→W first would re-litigate the transport laws and then R→R would
sit on top of statements still in flux.

**Easier to represent?**  R→R, by a wide margin: one deleted assignment
(`tv' = tv`), two per-hart fields, no new kind of step, visibility still a
prefix, the SC collapse at the top intact.  W→W needs a new global
component with environment nondeterminism in every arm, non-prefix
visibility, an AMO that no longer reads the flat cache, a DMA arm that no
longer reads `gmem`, and a fence that force-drains.

**More changes to existing proofs?**  W→W, by roughly an order of
magnitude.  R→R changes what a plain load mints and two whole-function
proofs.  W→W changes what a park/deposit/floor MEANS, and those are the
statements the tree is built on: `own_context` in 131 files, `ctx_floor`
42, `is_lock` 185, the box (1776 lines, ruled law), the lock protocol
(~5400 lines across `WpLock`/`WpSconfLock`/`ProofAcquire`/`ProofRelease`),
the ledger theory (~2700 lines), the virtio protocol (~10000 lines).

## 4. Effort

| stage | what | estimate |
|---|---|---|
| A. Machine + litmus | `D` in `gstate`, `visible` with drain, the AMO/DMA read change, release-class drain, `TsoMem`/`TsoLitmus` (MP/2+2W/S flip; CoWW, fenced variants) | 2–3 days |
| B. Interp + lifting | drained-set authority (a `gset nat` auth, monotone, receipts by inclusion), `tso_interp_at/of`, every arm's `∃ D' ⊇ D` and the generic interp update, the root sweep (same ~20 files as relaxed-rr B) | 3–4 days |
| C. Rulings | the parked forms, who upgrades, the box stamps or the lock row, the lock-word protocol's new state; review rounds in the endgame style | 1 week of review time, in parallel |
| D. Ownership laws | `TsoCtx` park/resume/deposit/absorb/dom with receipts, `TsoCtxAbsorbLb`, the FLOORS law instances, `CtxBox` floors, `SwtchCtx` pend-park, `SpecAcquire`/`SpecRelease` rows, every `_in` release spec that folds rows | 2–3 weeks |
| E. Racy tiers | `TsoMemPa` theory with `D`, `TsoCtxLedger` gates, `WpLock`/`WpSconfLock`/`ProofAcquire`/`ProofRelease`, `StartedInv`/`ProofMainSecondary`, `KptPublish`, `VirtioProto`/`DiskAvail`/`DiskInv`/`ProofVirtioDisk*` | 2–3 weeks |
| F. Close | full build, `audit-only`, notes | 2–3 days |

Total: **150–250 files, 6–10 agent-weeks with two or three agents after
the rulings; not a single-agent fortnight.**  For calibration the TSO port
ran 2026-08-24 → 09-03 with several agents and 27 review rounds, and its
ownership-layer redesign is the part this relaxation reopens.

## 5. What would make W→W cheap, if it is ever wanted

If the kernel's discipline "every cross-hart handoff is a lock release or
an acquire-fenced flag" were made a MODEL assumption — i.e. stores are
drained at every release-class fence and at every AMO, and never
otherwise (no environment drains) — then the drained set would be a
per-hart prefix (`dw_h = own_pub` at every sync point), "clean ⟹ drained"
would follow from "clean ⟹ published at a release", and most of §2 would
collapse into one extra conjunct on the release row.  But that model
forbids a store from ever becoming visible without a fence, which is a
behaviour hardware has, so a proof over it would not be sound for the
machine: "no hart passes `started` before hart 0's next release" would be
provable and false.  Recorded so nobody proposes it as a shortcut.
