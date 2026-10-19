VERDICT: NOT SATISFIED

# R45 — review of the route-P design (`notes/weak-allocproc-routeP-design.md`) against the code, P0(a) and P0(b)

Reviewer + design advisor (one-off, advisory: no proofs, no builds, no git/jj), 2026-10-19.  Read: the P design,
rulings [OWN.2] [OWN.105]–[OWN.111], `notes/W10-P0a-wfence.md`, `Weak/LitmusSBAcqP.lean` (753 l.), the last section
of `../xv6iris-weak-w3/PROGRESS-W10N2p.md`, R44 PART 0, `notes/W10-6m-census.md`, `notes/W10-K0-census.md` §3,
`Weak/GraphFabResidue.lean` (the four arms), the consumers of `ioResidueGmo` (grep: 40 files),
`Weak/WeakRvwmoKillIO(C).lean`, `Weak/CatRerouteIo.lean`, `Weak/SilOrd2.lean` (`enb :743`, `noStuckG :775`),
`MachCSL/Lang.lean` (`MState :97`, `fenceWv :217`, `MState.fence :227`, `silentOk :446`, `evStep :525`,
`hartStep :692`), `MachCSL/TsoMem.lean` (`fencePost :491`), `Xv6/AccessDiscipline.lean` (`racyValOk :314`,
`chainOkAt :328`, the ELEVEN conjuncts `:1106-1108`), `Xv6/KernelImage.lean` (`holding`/`acquire`/`release`
`0x80000bf2-0x80000d0a`, `ilock+0xe` `0x80003360`, `iunlock+0x1c` `0x8000341c`, `uartwrite+0x3a-0x76`),
`Weak/LockFacts.lean` (`fenceCensus :137`), `tools/ci/roots.txt`, `roots-weak.txt`, `kernel/fs.c`, `kernel/spinlock.c`.
Every size is an unverified estimate (ranges); every spec mark is w.r.t. riscv.cat / RVWMO / Sail / Zifencei / PMAs.

**Why NOT SATISFIED (in one paragraph).**  The design is sound in its machine half and I would launch its MachCSL
lane once P0(c) passes; what I would NOT launch as written is P-W3 (`noStuckP`): its progress lemma is FALSE on
xv6 executions (P0(a)'s `ip->ref` deadlock), its progress argument is stated over the wrong graph (§1 A2), and the
repair it needs is not the one the design's text implies.  **F-R45-1 (new, §2.1): the `ip->ref` deadlock is NOT a
FIFO (E1) problem** — a 3-hart RVWMO-consistent xv6 execution deadlocks the landing gate with NO FIFO edge at all
(two unsynchronized reads reordered on one hart), so a non-FIFO buffer would not remove it; the reader-side
exception at `ilock+0xe` / `iunlock+0x1c` (P0(a)'s Q-P-WFENCE-REF (a)) is required under EVERY buffer shape, and
with it `noStuckP` holds faithfully by a per-HEAD table of five static facts (§2.4).  Besides that: Q-6M-PTE (a) is
not moot (progress needs it), the narrow-δ1 "side condition" costs re-proofs not 0.1k (retire it inside P-M1
instead), and the (R1) finding is confirmed — P replays the UART chain without (R1), and dropping (R1) later is a
sized, non-blocking item (§3).  Required changes [R45.1]–[R45.8] in §6; owner questions in §7.
**Launch now regardless of this verdict:** P0(c) continues (w1); **P-W1** (`SbCand` with the landing policy as a
PARAMETER, §5) can start in any Weak slot today.

## 1. Audit of the P design against the code and the new evidence (spec first)

| # | design claim | code / evidence | mark | verdict |
|---|---|---|---|---|
| A1 | §1 row 4 / §3.4: FIFO is STRONGER than RVWMO as a machine, FAITHFUL for the quantifier iff `noStuckP`; `noStuckP` needs P-WFENCE: foreign-readable plain stores are WCrel or `lk->cpu` | P0(a): FALSE — `iget+0x58`, `idup+0x1c`, `iput+0x22`, `iput+0x8a` are foreign-readable (`ilock+0xe`, `iunlock+0x1c`: `fs.c` reads `ip->ref < 1` with no lock), not WCrel (the image has SEVEN fences, `fenceCensus`, none in `acquire`); the `lk->cpu` premise (b) is false too (FIFO-earlier set contains the previous `release+0x1a`; census §4.1) | — | **design wrong**; fix in §2 ([R45.1]) |
| A2 | §3.4: waits-for edges (E1)–(E6) with the measure "gmo position"; (E4) "a row's earlier unrealized event" | In a step-by-step walk ([OWN.106]) the ITEMS are the row HEADS and the landings; (E3) "a GF reader `r` of the co-predecessor" is not an item — the edge lands on the HEAD `e ≤po r` of `r`'s row, and `gmo(e) < gmo(w)` is NOT given (load-load reordering: `r <gmo e` is legal); (E4) is this hop, not an edge.  The design says as much in one clause ("the new case … is a RACY read … a census site again") but neither states the head table nor defines the measure for fence/fabric heads | FAITHFUL once stated | restate (§2.4, [R45.2]) |
| A3 | §3.2: [OWN.108] subsumed (no stale replay, no per-site view/value datum) | Correct under P: the gate holds back the overwriting landing, the member reads the landed top.  The landed `SilOrd2.enb :743` (iii) ("source realized, replayed stale") is replaced, not reused; the ruling text of [OWN.108] is superseded — tell the owner (§7, informational) | FAITHFUL | ok |
| A4 | §3.5: Q-6M-PTE moot ("values agree by construction") | Values yes; PROGRESS no.  A software walk / walker read of a user PTE (9 sites, census §3.4) is a plain read; under P it is a head gated on "source landed"; that its source is never pending needs the GF-level custody chain (`p->lock` hand-off, fenced release) — exactly Q-6M-PTE (a) (0.3–0.6k).  P0(a) §4.4 says the same for the stores | FAITHFUL | reinstate ([R45.3]) |
| A5 | §2.4: `pendOne` "discharged in the rule's own proof … the Xv6 call sites do not see it" | True for full-fraction and custody classes, but the FACT "no foreign PENDING entry on the bytes I just acquired" must be DELIVERED by the hop: the previous holder's stores to the protected bytes precede its release fence, so they are landed when the acquirer's AMO reads the landed release.  This is a corollary of `ctxLanded` the hop conversion must export (`pendOneOfCtx`); not in the design's P-M5 list | FAITHFUL | add ([R45.4]) |
| A6 | §2.3 `ctxLanded` (i): "A's own entries ≤ Vb A land before `t_rel` (FIFO)" | Under FIFO: immediate.  Under a non-FIFO buffer (§2.3 option (β)): from the release fence (`release+0x16` `fence rw,w` adjacent to `+0x1a`, `LockFacts.relAdj`; `main+0xac` before `started`): every own entry issued before the fence lands before entries issued after it (rule 4).  Either way the release rule must STATE it; under (β) the `fence rw,w` rule (`WpLock.lean:36` `_rw_w`, today "unchanged") mints the token | FAITHFUL | state ([R45.4]) |
| A7 | §1 row 5 / §2.2: an `.aq` AMO does not drain; its write lands at once; same-address own pending entries are drained by the exclusive READ | riscv.cat: rule 1 orders the own store before the AMO's WRITE; nothing orders it before the AMO's READ (forwarding).  The drain is a machine strengthening, harmless for the quantifier (the read returns the same value; only the read's gmo slot differs — a different mo witness, same rf/co) — but the progress measure for a drain-blocked exclusive head must be the pair's WRITE position (§2.4 H5) | machine STRONGER (harmless), quantifier FAITHFUL | note in §1 row 1 |
| A8 | §1 I/O row: MMIO neither buffered nor draining; a pending RAM store may land after a later MMIO store | FAITHFUL to the appendix "I/O Ordering" (c1) + PMAs; Sail drops i/o fence bits (D48).  This is what makes §3 (the UART chain) replayable | FAITHFUL | confirmed (§3) |
| A9 | §3.6 (a): registered W4 re-proof — "a pf `LStore` row = issue + land; `MRun` has no per-step thread constraint" | `machRunOfPfRun` (`MachOfPf.lean:2958`) relates RUNS, but its `simStep` shape (one pf step ↔ one `hartStep`?) is not checked in the design; if 1:1, P-W5 needs a two-step stutter lemma or a fused `issueLand` arm (+0.1–0.3k) | — | P0(c) item 6 ([R45.6]) |
| A10 | §1 last row / §8 Q-P-δ1: δ1 kept dead with `σ.sb cpu = []`, "≈ 0.1k inside P-M1" | The δ1 arms (`xstale`, `wv`, `fenceWv`, `afterExclStale`, `silentOk`, `storeSilent`, `staleFree`, `staleBlocked`, the acquire rule's stale outcome, W4's and Vtest's stale cases: inc 15–16b ≈ 3–5.5k) sit in every file P-M1..M8 re-proves; a side condition is a new case split in each stale lemma: +0.3–0.8k, not 0.1k.  §4 below: retire INSIDE P-M1 | sound either way | re-size ([R45.5]) |
| A11 | §0 F-P1 / §4: the UART chain is `ioResidueGmo`-inconsistent only through (R1); P replays it without (R1) | P0(b) `SBAcqP.uIoNo`, `uNoR1Ok` machine-check the first half; the replay walk-through in §3 confirms the second (the design's §4 table omits hart 2's continuation, which is what makes `L(w‴)` reachable — add it, [R45.7]) | (R1) STRONGER than RVWMO+PMAs | confirmed |
| A12 | §6: statement text, trusted base, roots unchanged; MachCSL-tier roots re-proved under the [OWN.105] precedent | `roots.txt` (15 Xv6/MachCSL roots) + `roots-weak.txt` (13): statement text unchanged; `tcb/expected.json` module set unchanged if `lp`/`sb` live in `Lang.lean`/`TsoMem.lean` | FAITHFUL | ok |
| A13 | §2.1: "a byte holding ANOTHER hart's pending entry: the issue step chooses the position nondeterministically; for xv6 never (`pendOne`)" | Checked for the racy classes: `ip->ref` writers are under `itable.lock` (the previous writer's store precedes its release fence; the next writer's AMO reads the landed release ⇒ landed); `lk->cpu`: holder only; `started`: hart 0; PTEs: owner.  OK | FAITHFUL | ok |

Spec standing of the whole design is unchanged by this review: nothing here changes what RVWMO / riscv.cat / Sail /
Zifencei / PMAs say.  The ONLY place the design was wrong about the SPEC-vs-xv6 relation is A1 (which executions
RVWMO admits on `ip->ref`), and the census's two executions plus F-R45-1 below are the corrections.

## 2. The `ip->ref` landing deadlock — root cause and the fix

### 2.1 F-R45-1: the deadlock is a READER-side problem, not an (E1) problem

P0(a) §4.3's two executions close the cycle through the FIFO edge `land w →E1 land w′`.  Here is a third,
RVWMO-consistent, with NO FIFO edge, built from the same `namex`/`iput` traffic (byte `ref` = `dp->ref`, lock
`lk` = `dp->lock.lk`, the sleeplock's inner spinlock; three harts A, B, C all holding a reference to `dp`):

* **A**: `iunlockput(dp)` → `releasesleep` → `release(&lk)`: `fence rw,w`; **`Y` = `sw zero` on `lk`**; then
  `iput(dp)` → `acquire(&itable.lock)` (`amoswap.w.aq`, no fence) → **`w` = `ref--`** (`iput+0x22`).
* **B**: `ilock(dp)`: **`e_B` = `ilock+0xe` reads `ref` = `w`** (A's decrement); `blez`; `acquiresleep(&dp->lock)`
  → `acquire(&lk)` → `push_off` → `holding(&lk)`: **`r_B` = `holding+0x0` reads `lk.locked` = 1** (A's acquire
  write in `releasesleep`, the co-predecessor of `Y`; stale).
* **C**: `ilock(dp)` → `acquiresleep` → `acquire(&lk)` → **`e_C` = `holding+0x0` reads `lk.locked` = 0 = `Y`**;
  `amoswap.aq` takes `lk`; … later `iunlock(dp)`: `holdingsleep` → `acquire(&lk)` … → **`r_C` = `iunlock+0x1c`
  reads `ref` = `w₀`**, the value BEFORE A's decrement (stale w.r.t. `w`).

gmo witness: `r_B < Y < e_C < r_C < w < e_B`.  Load value: `e_B` reads `w` (gmo-before, co-max), `r_B` reads the
1 (`Y` not yet), `e_C` reads `Y`, `r_C` reads `w₀` (`w` not yet).  ppo on B: `e_B <po r_B` but nothing orders
them — `lw ref` → `blez` → `jal acquiresleep` → prologue stores → `jal acquire` → `push_off` (csr ops, per-cpu
loads/stores) → `holding`: `lw lk.locked`; different addresses, no fence, no `.aq`, no address dependency, and
rule 11 orders `ctrl;[W]` only (the per-cpu STORES are ordered after `e_B`; the LOAD `r_B` is not).  On C,
`e_C →ctrl amoswap.aq →(rule 5) r_C`, so `e_C <gmo r_C` is forced and satisfied.  On A, `Y <po w`: ordered or not,
the witness has `Y < w`.  `rvwmoCatConsistent` holds (a `decide +kernel` leaf like `SBAcqP.l3Cat` would confirm it:
[R45.s2]).  This is IRIW-with-load-reordering specialised to xv6: one hart's unsynchronized read of a count
satisfied AFTER its program-later read of a lock word.

**The P walk (design §3.2 gate, FIFO or not):** head B = `e_B`, gated on `land w`; head C = `e_C`, gated on `land
Y`; `land Y` waits (E3) for `r_B`, an unrealized GF reader of `Y`'s co-predecessor, which is behind `e_B`; `land w`
waits (E3) for `r_C`, behind `e_C`.  A eventually blocks at its next same-address drain (`acquire(&itable.lock)`
against its pending release).  No item is enabled: **`noStuckP` is false, and no FIFO edge was used** — under a
non-FIFO buffer (§2.3 (β)) `land w` and `land Y` are independent and the cycle is identical.  So the obstruction is
the pair (`e_B`, `r_B`): a racy read that may be a BLOCKED HEAD, program-before a stale-reading read of another byte
that RVWMO lets be satisfied earlier.  Among the census's 18 kernel sites this pair exists ONLY for `ip->ref`
(§2.4 table H3): `holding+0x0`/`+0x12` are followed by a control-dependent `amoswap.aq` before any other read,
`started` by `fence r,rw`, the PTE reads are custody-chained (never pending), the device-side reads are fabric
members or read device stores (landed at once).

### 2.2 The fix — the two-site reader exception (P0(a)'s Q-P-WFENCE-REF (a)), required under every buffer shape

**Statement sketches (Weak; the machine is untouched — a read at the landed top is an ordinary MachCSL plain read
at `tvn = ltop`, always legal since `tv ≤ ltop`).**

```lean
/-- the two value-insensitive racy reads (`fs.c` `ip->ref < 1` guards; census 6m §3.3; P0(a) §5) -/
def ipRefPc (pc : Int) : Bool := pc = KernelSyms.ilock + 0xe || pc = KernelSyms.iunlock + 0x1c
def ipRefRd (GF : Gfexec) (e : Geid) : Prop := gisR e ∧ ipRefPc (pcOf GF e)      -- pc from the emission state

inductive SbOrd.enb (GF D fab) (S) (cnt) : Item → Prop
  | fab   : …                                                                   -- unchanged
  | rd    : gisR e → ¬ ipRefRd GF e → (∀ b, srcOf GF e b = some w → landedOrOwn S x w b) → enb (.ev x)
  | rdX   : ipRefRd GF e → enb (.ev x)      -- NEW: no source gate; the member reads the landed top / own pending
  | wr | plain | land : …                                                       -- unchanged

/-- value agreement: exact everywhere except at the two pcs, where both words are in [1, 2^31) -/
def SbAgree.valEqX (GF) (S) : Prop :=
  ∀ r ∈ realized S, (¬ ipRefRd GF r → memberBytes S r = gfBytes GF r) ∧
                     (ipRefRd GF r → irefOk (memberWord S r) ∧ irefOk (gfWord GF r))
/-- the one value lemma, used on BOTH sides (GF co and the member's co-PREFIX of it): every write to `ip->ref`
    co-between the reader's own last `ref++` and any write the reader can see is an `itable.lock`-protected
    ±1 of a count that includes the reader's reference, hence ≥ 1 -/
theorem irefGe1 (GF) (B : row) (x : write of ref) : ownInc GF B ≤co x → x ≤co srcOf GF e_B → irefOk (val x)
/-- datum: the registered lockstep datum with TAINT at the two sites (`CertZ13.relT`, `CertZ11.loadTail`):
    the loaded register (`a5`) feeds only `blez` (`ilock+0x10`, `iunlock+0x1e`); `decide +kernel` over the two
    successor sets (6m's taint walker restricted to two pcs, or two hand proofs) -/
theorem ipRefTailDies : ∀ pc, ipRefPc pc → loadTailDies pc {a5}
```

Member-side `irefOk`: the member's landed writes to `ref` are a GF-co PREFIX (the walk invariant), the reader's own
`ref++` (`iget+0x58`/`idup+0x1c`, program-before `e`) is landed or forwarded, and every landed write co-after it is
in `irefGe1`'s interval — so the top the member reads is ≥ 1.  (`racyValOk` of the export says the same at the
realized MachCSL state for an unchained foreign entry; the GF lemma is the one to prove, it serves both sides.)

**Why progress then holds** (the full skeleton is §2.4): with `rdX`, an `ip->ref` read is never a blocked head, so
the pair (`e_B`, `r_B`) cannot start a cycle; every other racy head is gmo-before its row's later reads by a static
hop (H3 table), every landing edge is gmo-backward, and the FIFO edge (E1) is either absent ((β)) or covered by the
WCrel census + the `lk->cpu` reader-side lemma ((α)).  In F-R45-1's execution the walk is: `e_B` (reads `w₀`, ≥ 1,
tainted until `blez`), `r_B`, `L(Y)`, `e_C`, …, `r_C` (reads `w₀` = GF), `L(w)`, `e_B`'s taint already dead.

**Spec marks.**  (a) the exception: FAITHFUL (the GF is admitted; only the member's value at a value-insensitive
read differs, and the published statement speaks of GF's values through the kill, not the member's);
(b) a NAMED premise excluding these GFs: WEAKER and FALSE-ish as a header item (they are reachable xv6 behaviours);
(c) a kernel change (`ref` read under `itable.lock`): out of scope [OWN.4].  (a) it is; owner confirmation in §7
(Q-P-WFENCE-REF).  Cost: `rdX` + `valEqX` + `irefGe1` + the two-site taint ≈ +0.5–1.0k on P-W2/P-W3 over the
design (of which `irefGe1` 0.2–0.4k and the taint 0.15–0.3k were already in row 6m's budget).

### 2.3 Other foreign-readable non-WCrel store classes (the (E1) half, FIFO only) — and Q-P-FIFO

Under the design's FIFO the (E1) edge `land w → land w′` (`w′` FIFO-before `w`, no fence between) is not
gmo-backward; P0(a) lists the classes: `ip->ref` (closed by §2.2: nothing foreign ever WAITS on `land w` for an
`ip->ref` store once the two readers are ungated — chained readers' sources are landed when their acquire is
realized), `lk->cpu` (acyclic by the READER-side argument of census §4.1: after `holding+0x12` a non-holder issues
only own-stack accesses and failed AMOs until its `.aq` AMO — a static fact about `acquire`'s text, 0.2–0.4k),
`initlock` (unpublished), PTE stores (chained given custody, A4).  So under FIFO `noStuckP` carries THREE static
inputs: the WCrel census (`decide +kernel` over `textPcs`, S–M), the `lk->cpu` reader lemma, and PTE custody.

**Option (β), a per-address + fence-order buffer ("P-set").**  Replace the FIFO by what RVWMO actually orders among
a hart's plain stores: rule 1 (same address) and rule 4 (a `pw ∧ sw` fence between them).  MachCSL:
`sb : CPU → List (Nat × Nat)` (issue stamp, fence EPOCH), `sbEp : CPU → Nat` bumped by every `pw ∧ sw` fence
(`rw,w`, `w,w`, `rw,rw`, `w,rw`, `tso`; the draining ones empty the buffer anyway);
`landOk σ cpu t := (t, ep) ∈ σ.sb cpu ∧ (∀ (t', ep') ∈ σ.sb cpu, t' < t → ep' = ep ∧ ¬ overlaps t' t) ∧ ¬ othersReserve …`.
`histOkP` keeps its shape (per byte the same author's entries still land in issue order); `ctxLanded` (i) comes
from the epoch (A6): `release+0x16` / `main+0xac` sit between the context's stores and the release store.  Twin:
`msSb : Nat → List (Wmsg × Nat)`, `land i k` picks any landable pending message.  Then EVERY (E1) edge is
gmo-backward (rule 1 / rule 4) and the three static inputs above shrink to PTE custody alone.
Spec: FAITHFUL as a machine too (2+2W and unfenced MP become machine behaviours, exactly RVWMO's store side); the
Xv6 WP proofs need no same-hart W→W order that is not fence-covered (publication = `started` after `fence rw,w`,
every hand-off = a release; pipe/file objects are published through releases) — the one place to check is the
release rule's new premise (A6), discharged at `release`/`main` once.
Cost: +0.3–0.6k MachCSL (epoch field, `landOk` predicate, `landedBeforeOfEpoch`, the fence token), +0.1–0.2k Weak
(epochs in `SbCand`), −0.3–0.7k Weak (no WCrel leaf, no `lk->cpu` reader lemma, no (E1) case in `noStuckP`): NEUTRAL in
lines, cleaner progress proof, no census dependency for the writer side.  It does NOT replace §2.2 (F-R45-1).
**Against it:** [OWN.110]'s text says FIFO; the `ctxLanded` proof (the riskiest P-M2 piece) gains a case; the FIFO's
three static inputs are cheap and two are already written up.  **Recommendation: (β)** for faithfulness and
robustness, decided by P0(c)'s measurement (make `landOk` a parameter so the choice costs nothing to defer); FIFO +
census is the fallback.  Owner question Q-P-FIFO (§7).

### 2.4 `noStuckP` restated — items, edges, measure, and the per-head table (replaces design §3.4; [R45.2])

**Items** at a walk state: `head x` (row `x`'s next GF event `e_x`) and `land(x, w)` (a pending store of row `x`).
**Edges** (A waits for B): (E5) `head x` → `land s`: `e_x` a gated read with a FOREIGN pending source `s`;
(E6) `head x` → `land w` (own): `e_x` a draining fence / `.rl` / an exclusive read overlapping `w`;
(E2w) `head x` → `land w0`: `e_x` an exclusive write whose co-predecessor `w0` is pending;
(E3w) `head x` → `head y`: `e_x` an exclusive write with an unrealized GF reader `r` of its co-predecessor on row `y`;
(Efab) `head x` → `head y`: `e_x` a fabric member not next in fabric order, row `y` holds the next one;
(E1) `land w` → `land w′`: `w′` FIFO-before `w` (FIFO) / overlapping or earlier-epoch (β);
(E2) `land w` → `land w0`: foreign co-predecessor pending; (E3) `land w` → `head y`: unrealized GF reader of the
co-predecessor on row `y`.
**Measure** µ: `µ(land w) = gmo(w)`; `µ(head x) = gmo(e_x)` for a memory or I/O event (I/O events are `gmem`);
for a FENCE head, the gmo position of the row's first memory event after the fence (a fence head with none has
only (E6) edges and is on no cycle); for a drain-blocked exclusive-READ head, the position of the pair's WRITE (A7).
**Claim: every edge strictly decreases µ, hence the waits-for graph is acyclic and some item is enabled.**
(E5) rf ⊆ gmo; (E6) rule 4 / rule 6 / rule 1 (to the pair's write); (E2w),(E2) co ⊆ gmo; (E1) census (FIFO) or rule
1/4 (β); (Efab) (R3) of `ioResidueGmo` — the one trusted arm the proof uses; (E3w),(E3): `r <fr w` gives
`gmo(r) < gmo(w)` (`SBAcq.frLt`), and the HEAD `e_y ≤po r` needs **`gmo(e_y) ≤ gmo(r)`** — the per-head table:

| head kind | why `e_y ≤gmo` every later read `r` of its row | status |
|---|---|---|
| H1 `.aq` AMO (every kernel AMO: `acquire+0x1c`, G1 `kernelAmoAq`) | rule 5 | static, planned (6l G1) |
| H2 draining fence | rule 4 (`pw ∧ sr`) | by definition of µ |
| H3 gated plain read with a pending foreign source = a RACY site: `holding+0x0` (acquire path, pending release), `holding+0x12` (pending `lk->cpu`), `main+0x16` (`started`), `ip->ref` ×2, PTE ×9, `virtio_disk_intr` ×4, device `DRead` ×8 | `holding+0x0/+0x12`: `→ctrl amoswap.aq` (rule 11, the AMO is a write) `→(rule 5)` every later read — no read between (`li a0,0; ret; bnez; amoswap`); `started`: `fence r,rw` (rule 4); **`ip->ref`: FAILS (F-R45-1) → never a head by `rdX`**; PTE: custody ⇒ source landed ⇒ never blocked; `virtio_disk_intr`: sources are device stores (land at once) ⇒ never blocked; device `DRead`: fabric member (Efab) | static per site; one exception |
| H4 fabric member | (R3) | trusted arm |
| H5 drain-blocked exclusive read (walker A/D pair on an own pending PTE) | rule 1 to the pair's write; readers of the PTE's co-pred are custody-chained | custody (A4) |

Inputs of `noStuckP`: `rvwmoCatConsistentT`, `ioResidueGmo` ((R3) only), the image (H1/H3 `decide +kernel`),
`kernelAmoAq`, PTE custody at the realized prefix (6m F4 (a)), and under FIFO the WCrel census + `lk->cpu` reader
lemma.  NO named premise.  Confidence M (was M−): the obstruction is now understood and the table is finite.

## 3. (R1) — can P, as designed, replay RAM-store → MMIO reorderings?  Yes.  What would block dropping (R1) later

**Replay.**  An MMIO access is an inert `LIo` step (`MStepIo`, no message, no view move) realized in fabric order
(`fab` arm); a plain RAM store issued before it stays PENDING across it (the design's I/O row: MMIO neither buffered
nor draining — FAITHFUL to appendix (c1) + PMAs; Sail drops the i/o fence bits, D48).  The UART chain (K0 §3 /
P0(b) §2) under P, with the continuation the design's §4 omits: hart 2 `I(w‴)` (pending), `A_tx` (lands),
LSR read, `X` (fabric), `release(tx)` (`fence rw,w`: NO drain; `sw zero tx` pending, FIFO/epoch after `w‴`),
loop → `sleep_prepare` → `acquire(P2.lock)`: an exclusive read of the byte holding pending `w‴` ⇒ **same-address
drain: hart 2 blocks on `L(w‴)`**; hart 1 `LSR₁` (fabric, after `X`), `consoleintr`, `I(R_y)`; hart 3 `A_y3`
[`wr`: `L(R_y)` first — its co-pred's readers are hart 1's own, realized; its FIFO/epoch predecessors are fenced],
`r3 = holding+0x0` reads 1 = GF (source `A_z2`'s write, member-latest since `w‴` is pending), failed swaps …,
then GF's hart 3 reads 0 ⇒ gated on `L(w‴)` ⇒ `land` arm: every reader of `w‴`'s co-pred realized ⇒ `L(w‴)`,
hart 2 unblocks.  Hart 1's later `acquire(tx)` (in `uartintr` after `consoleintr`), if GF has it read hart 2's
pending `sw zero tx`, waits on `L(w‴)` too (FIFO) — hart 3 does not wait on hart 1, so no cycle.  **P needs neither
(R1) nor (R2) for this; it needs (R3) (fabric ⊆ gmo) for H4.**  [OWN.111]'s premise is confirmed.

**Remaining uses of (R1) that would block dropping it (inventory from the tree; informational; sizes unverified):**

| # | use | file:line | what replaces (R1) | size |
|---|---|---|---|---|
| U1 | the I/O-window entry `entry <gmo x`: `ioSegPinned` (W13 (K) §7 "Claim L-IO"), `ioSegAfterIoC`, `gpoOfGmo` ("a same-hart write gmo-after `x` is po-after it — po-before would put it gmo-before `x` by (R1)"), `ioWinRelGmo`/`ioSegCertRrC` (W11-B re-route) | `WeakRvwmoKillIO.lean:612-650`, `WeakRvwmoKillIOC.lean:300-316,455-470`, `CatRerouteIo.lean:60-70` | the re-route needs only `entry <gmo REL`: the device lock's release `fence rw,w` (rule 4, pr∧pw → sw) gives it at every release site without `x` (`CatRerouteIo` deviation (1) chose (R1)+(R2) over the fence); `gpoOfGmo`/`afterIo` is the (K-cat′) closing-step invariant that W11-B made unnecessary for the published route — verify dead, else M | 0.3–0.8k (+0.5–1k if `afterIo` is live) |
| U2 | `CertZ17` NF3/NF4 anchors (fabric-member RAM write before later lock-byte writes) | `CertZ17.lean:21` | RETIRED by 6l (`SilOrd2`; `orderSupplyCZ3`/`lockDiscCZ3` gone) | 0 |
| U3 | the DISK row (`y.1 = NCPU`): DMA reads po-before START/POP | `GraphFabResidue.lean:12-18` | device-MODEL semantics, not ISA: keep as a disk-row-only arm `(R1-dev) … ∧ x.1 = NCPU` — a trusted-text split, re-audit | 0.1–0.2k |
| U4 | `linCandDiskLat`/`ancOkIO` (W11 (iv)c) | `RvwmoXv6ScaT.lean:857-872` | consumes the disk-row arms + `gdiskRead14`: unaffected by dropping the HART-side (R1) | 0 |
| U5 | premise plumbing + (R3) for fabric progress/anchors: `SilOrd2 :561,611,1185`, `CertZ23`, `GraphFetchN2/WalkZ/Kill/AncSupply`, `CapFetchProv :121-243`, `LockFacts3 :181-255` | — | unchanged (they pass `ioResidueGmo` down and use (R3)/(R2)) | 0 |
| U6 | ≤ 2 mentions each: `CertZ15/16/19/25`, `SilWalk2`, `SilSiteStep`, `SilKill(T)`, `CertZ3/7/9/31/33/34`, `WeakRvwmoTopo/Acyc`, `GraphFabConf`, `PfStepTsoView` | grep | to be inventoried arm by arm (most are `ioResidueGmo` as a hypothesis name) | 2–4 h |

Total to drop (R1) from the hart rows after P: ≈ **1–2.5k, 8–20 h, M**, after P-W3 and on the W11-B re-route;
(R2) and (R2′) stay (also stronger than the ISA; not P's business).  Record as after-capstone item **A4** ([R45.7]).
Note for the plan's §B(11b) sentence "(R1)/(R2) ISA-given at three xv6 sites": with D48 (i/o fence bits dropped) no
in-tree site is ISA-given — all of (R1) is platform text today ([R45.s3]).

## 4. Q-P-δ1 — narrow δ1's merged stale-silent-AMO arm under P

Under P a failed acquire reads the LANDED top (the release has not landed ⇒ 1): the stale arm is never used by the
replay (design §1 last row, correct).  Three options:
(a) **keep dead with `σ.sb cpu = []`** (design): sound (with an empty buffer issue = landing positions, `wv`/`ownPub`
coincide); cost is NOT 0.1k — every stale lemma P-M1..M8 re-proves gains a case (A10): +0.3–0.8k inside the lane;
(b) **retire in row 8 after P**: pays (a) AND a second strict audit (0.3–0.6k deletions + 4–8 h);
(c) **retire INSIDE P-M1** (the same `evStep`/`MState` edit, the same strict audit): deletions only
(`xstale`, `wv`, `fenceWv`, `afterExclStale`, `silentOk`, `storeSilent`, `staleFree`, `staleBlocked`, the four
`not_silentOk_*`/`staleFree_*` lemmas, `blockedStep`'s stale arm, `WpLock`'s stale acquire outcome, `MachOfPf`'s
and Vtest's stale cases); P-M2..M8 never meet them; `MState.fence` loses its `wv` line.
Consequences for registered roots: NONE beyond P's own (statements unchanged; every MachCSL-tier root re-proved
under the [OWN.105] precedent; `baseline.json` opaques unchanged; the Weak roots M1/M2 re-registered by P-W5 with a
SIMPLER `simStep`).  Rulings touched: [OWN.105] superseded by [OWN.110] for its purpose; [OWN.109] moot; [OWN.103]'s
"keep δ1 in mind" fallback is history (jj) — the P lane lives on a branch until P-M8, so nothing merged loses δ1
before P works.  Spec: FAITHFUL under all three ((a)/(b) keep one extra harmless behaviour).
**Recommendation: (c).**  Owner question Q-P-δ1 (§7).

## 5. Updated increment plan (lanes, sizes, hours, dependencies, confidence)

Rates as the plan's: MCSL cone 6–10 h/k, Weak leaves 4–8 h/k, + acceptance.  Acceptance gate for every MCSL
increment: `lake build MachCSL Xv6 Weak Vtest` green, `audit.sh` (+ `--weak --build`) baseline/opaques unchanged,
`tcb.sh` (module set moves at most once), `#print` signatures of every registered root textually unchanged.

| # | increment | lane | lines | h | depends | conf. | acceptance / notes |
|---|---|---|---|---|---|---|---|
| P0(c) | **MachCSL churn spike (RUNNING, w1, scratch branch)** — must show, before the MCSL lane commits: (1) `interp_land : machInterp σ ⊢ \|==> machInterp (σ.land cpu)` PROVED over the minimal interpretation (`histBytes` + `lpAuth` + `sbAuth` + `histOkP`) with NO client-visible frag changed (ghost-invisibility); (2) a CHURN TABLE: per file (`TsoMem`, `WordHistDefs/WordHist`, `ChainDefs` (126 sites), `KptInv` 25, `Lock` 22, `UEpoch*` 17, `Reserved` 7) the number of lemmas whose STATEMENT changes vs proof-only; **go/no-go: statement churn in `ChainDefs`+`KptInv`+`Lock` > ≈120 lemmas, or `interp_land` needing a client-facing change ⇒ STOP, re-size P-M4 at ×1.5 and re-ask**; (3) `wp_s_sw` with the Xv6-facing statement unchanged + `pendOne` from a full-fraction frag; (4) `read_cases`/`heads_eq` with `visibleAt`; (5) `landOk` as a PARAMETER with both instances (FIFO; per-address + epoch) type-checking; (6) `MachOfPf.simStep` multiplicity (A9); (7) the Löb shape of the land arm (`wpLoop_restart*`), statement only | spike | 0.3–0.6k scratch | 10–18 | — | H | report ≤ 2 days; decides P-M1's state shape and Q-P-FIFO's cost |
| P-M1 | `TsoMem`/`Lang` state + arms (design) **+ δ1 retirement (c) + the epoch field if (β)**; Vtest `XState` | MCSL | 0.6–1.1k | 5–11 | P0(c) PASS, Q-P-FIFO, Q-P-δ1 | M+ | builds; `MState.store` kept for exclusive writes |
| P-M2 | interpretation: `lpAuth`/`landedAt`, `sbAuth`, `pendOne`, `ctxLanded` (+ the epoch case `landedBeforeOfEpoch` if (β)), `histOkP`; `interp_land`; `mmOk`/`rsvOk`; `Adequacy` | MCSL | 1.1–2.0k | 9–20 | P-M1 | M− → M after P0(c) | `riscvPowerAdequacy` green |
| P-M3 | lifting + base memModel lemmas (design) | MCSL | 1.0–1.6k | 8–16 | P-M2 | M | `Wp`, `WpAtomic` green |
| P-M4 | history layer + export sub-definitions over `lp` (incl. `dynLockWinZAt`'s window, `ksFrameAt`) | MCSL | 2.0–3.5k | 15–35 | P-M3 | M− | `AccessDiscipline` + `LinkDiscAdequacy` green; conjunct list unchanged |
| P-M5 | contexts/hops **+ `pendOneOfCtx`** (A5) | MCSL | 0.9–1.6k | 7–16 | P-M4 | M | `CtxBox` green |
| P-M6 | locks: release rule states "my stores before the fence land first" (FIFO: from `sbAuth`; (β): the `fence rw,w` token, `wp_s_fence_rw_w` mints it, discharged at `release`/`main+0xac`); acquire reads the landed top (+ the new failed-spin case); `lockWinAt`/`lkFold` readings | MCSL | 1.5–2.6k | 10–26 | P-M5 | M− | `WpLock`, `Xv6/Spin*`, `Sleeplock` green |
| P-M7 | store/fence/device rules (design) | MCSL | 0.8–1.4k | 6–14 | P-M6 | M | 219 call-site files rebuild with ≤ mechanical edits |
| P-M8 | Xv6 fallout, Boot, Vtest policy, docs, full acceptance | MCSL | 0.9–1.8k | 8–18 | P-M7 | M | all roots re-proved; `tcb.sh` |
| **P-W1** | **`SbCand`** with `landOk` a PARAMETER (FIFO / per-address+epoch), run, embedding `execWfOfOld`; `LitmusSBAcqP` promoted; **+ the F-R45-1 witness `l4Cat`/`l4NoMemberP`** ([R45.s2]) | Weak | 0.6–1.1k | 4–9 | — (**launch now**) | M+ | the litmus members by `decide`; the F-R45-1 GF cat-consistent and gate-deadlocked by `decide` |
| P-W2 | `SbWalk`/`SbReplay`/`SbAgree`: `valEqX`, the `rdX` arm, `irefGe1`, the two-site `loadTail`, lockstep datum at `relT` (`CertZ9/13`) | Weak | 1.1–1.9k | 6–14 | P-W1 | M | `agreeW4` with `nf = True` except the two pcs (tainted-lockstep) |
| P-W3 | THE GATE + **`noStuckP` per §2.4** (items/edges/µ, head table H1–H5, `kernelAmoAq`, PTE custody from 6m F4 (a) 0.3–0.6k; FIFO only: WCrel `decide +kernel` leaf 0.1–0.3k + `lk->cpu` reader lemma 0.2–0.4k); `walkPolP`, `walkRunP` | Weak | 1.5–2.8k ((β): 1.3–2.4k) | 10–22 | P-W2, Q-P-FIFO (the (E1) sub-case only) | **M** (was M−) | `noStuckP` with NO named premise (fallback: NAMED, WEAKER, 0) |
| P-W4 | kill glue (design) | Weak | 0.8–1.4k | 5–11 | P-W3 | M | `t2linSupplyCZTtagged` consumes it |
| P-W5 | registered W4 re-proof (FIFO-empty invariant; stutter/fused arm per A9), M1/M2 re-registration | Weak (after P-M8) | 0.8–1.5k | 6–12 | P-M8 | M+ | `audit --weak --build` 13 roots green |
| P-W6 | buffered twin W4-P (`rmemP`: `R-sb` (+epochs), `R-lp`), `recRealizedP`; CapF6–10's `readAt` at the member (feeds 6b, 6j E1) | Weak | 1.5–2.5k | 10–20 | P-W5, P-W2 | M− | `segRealized`/`readAt` at `SbCand` members |
| **Σ P** | | | **15.0–26.7k** (MCSL 8.8–15.6k serial, Weak 6.2–11.1k) | **108–243** | | **M−** (machine M− until P0(c); progress M) | |

Order: P0(c) (w1, running) ∥ **P-W1 now** → P-W2 → P-W3 ∥ the unaffected rows 6a/6c/6d/6e/6g/6h/6b′; P-M1 only
after P0(c) PASS + Q-P-FIFO + Q-P-δ1 (one owner menu); P-M1..M8 serial (≈ 4–7 calendar weeks of one slot);
P-W5/P-W6 after P-M8.  Row 6m under P = `irefGe1` + two-site taint (inside P-W2) + PTE custody (inside P-W3) + the
lockstep-datum glue 0.3–0.8k; the chain-based race-free-read theorem (6m F6) is retired (`valEqX` is it).
Σ remaining ≈ 23.2–45.3k (mid ≈ 34k): P 15–26.7k + the rest 8.2–18.6k; ≈ 140–390 h; % done by lines ≈ 78 % (74–84 %),
unchanged from the design within its own noise.  By files: unchanged from the design (MCSL ≈ 45–60 of 293 MachCSL +
30–40 of 2138 Xv6; Weak +10–14 leaves).

## 6. REQUIRED changes [R45.n] (to the design note / plan rev 55)

**[R45.1] Replace P-WFENCE by the two-site reader exception (§2.2) and record F-R45-1.**  §3.4's "(E1) is the new
risk … P-WFENCE" paragraph is wrong twice (the `lk->cpu` premise (b); the claim that the (E1) census settles
progress).  Text: "`noStuckP` needs (i) the `ip->ref` exception `rdX` (F-R45-1: required under FIFO and non-FIFO),
(ii) the per-head table H1–H5, (iii) PTE custody, and under FIFO (iv) the WCrel census + the `lk->cpu` reader-side
lemma (census §4.1)."  `SbAgree.valEq` → `valEqX`; the datum is `relT`-lockstep with taint at two pcs.

**[R45.2] Restate the progress argument per §2.4** (items = heads + landings; the edge list; µ with the fence /
drain-blocked-exclusive cases; the head table as the per-site obligations; (R3) as the one trusted arm used).

**[R45.3] Q-6M-PTE (a) is NOT moot**: keep it as a P-W3 dependency (progress of PTE-read heads, H3/H5), 0.3–0.6k;
strike "Q-6M-PTE … moot" from §3.5.

**[R45.4] P-M5 gains `pendOneOfCtx`; P-M6 states the release rule's "earlier stores land first" fact** (FIFO: from
`sbAuth`; (β): the `fence rw,w` token minted by `wp_s_fence_rw_w`), discharged at `release+0x16`/`main+0xac`.

**[R45.5] Q-P-δ1: adopt (c) (retire inside P-M1) pending the owner; re-size (a) to +0.3–0.8k, not 0.1k.**

**[R45.6] P0(c)'s acceptance list and go/no-go (table row P0(c)), with `landOk` parametric and the `simStep`
multiplicity check; the MCSL lane does not start before P0(c) PASS.**

**[R45.7] §4 UART table: add hart 2's continuation (the same-address drain at its next `acquire(P2.lock)`) and
hart 1's `acquire(tx)`; §6: "the replay uses (R3) only; (R1) is not used by P"; new after-capstone item A4 "drop
hart-side (R1)" with the U1–U6 inventory (§3), 1–2.5k, after P-W3.**

**[R45.8] Rulings ledger in the plan: [OWN.108] superseded under P (no stale replay; the view/value datum is
vacuous); [OWN.105]/[OWN.109] superseded if Q-P-δ1 = (c); [OWN.111] confirmed with the §3 walk-through.**

Suggestions: **[R45.s1]** `Weak/LitmusSBAcq.lean` header "nothing imports this file" is stale (O-P0b-A).
**[R45.s2]** mechanize F-R45-1 in `LitmusSBAcqP` (`l4Cat` + "no gate-respecting P member": a `decide` over the
gate as `GateWr`/`ReadsGF` with the FOUR-row program; ≈ 0.2k) — inside P-W1.  **[R45.s3]** fix the plan's §B(11b)
"(R1)/(R2) ISA-given at three xv6 sites" (none in-tree under D48).  **[R45.s4]** P0(a)'s census tooling (the
scratch Python CFG pass) should be committed under `tools/` if the FIFO option is kept (the WCrel leaf's generator).

## 7. Owner questions (owner format; one or two per menu — in this order)

### Q-P-WFENCE-REF — confirm the two-site reader exception (the only faithful repair)

*Plain-language issue.*  xv6 reads an inode's reference count without a lock in two places (`ilock`, `iunlock`),
only to panic if it is below 1.  The hardware may let such a read be satisfied AFTER a later read of the same hart
(two loads of different addresses with nothing ordering them).  The route-P replay waits for a store to "land"
before anyone reads it, and holds a store back while someone still has to read the OLD value; with that unlocked
count read in the middle, three harts can each wait for one another and the replay stops — although the real
machine just runs on.
*Tiny example.*  Hart A decrements `dp->ref` right after releasing `dp`'s sleeplock.  Hart B reads the new count
(`ilock`), then, inside its own lock attempt, sees the sleeplock's spinlock still as "taken" (the old value).  Hart
C saw the spinlock released, took it, and later reads the OLD count in `iunlock`.  All three orders are legal
RVWMO; the replay needs A's count store landed for B, B's lock read done before A's release lands, C's lock read
done after it, and C's count read done before A's count store lands — a circle.
*Terms.*  *Land*: the moment a store leaves the hart's private buffer and becomes visible to all.  *Gate*: the
replay's rule for when a step may be taken.  *Value-insensitive read*: a read whose value only feeds a check both
possible values pass (here "≥ 1").  *Taint*: the proof's way of running a hart whose register holds a different
value until that register is dead.
*Options.*  **(a) Exempt the two reads from the gate** (they read whatever has landed — provably ≥ 1 on both
sides — and run tainted until the compare).  An xv6 expert reads: "the proof replays every behaviour exactly,
except that at these two sanity checks the replay may see a slightly older count; both counts pass the check."
FAITHFUL.  Cost +0.5–1.0k inside P-W2/P-W3 (mostly already budgeted in row 6m).  **(b) Assume such executions do not
happen** (a named premise).  Reads: "the theorem excludes some real RVWMO executions of xv6" — WEAKER, and the
excluded executions are reachable.  Cost 0.  **(c) Change xv6** to read the count under `itable.lock`.  Reads:
"the verified kernel differs here from upstream" — FAITHFUL but out of scope [OWN.4]; cost: kernel change + re-image.
Recommendation: **(a)**.

### Q-P-FIFO — a strict FIFO buffer (as ruled) or exactly RVWMO's store order (same address + fences)?

*Plain-language issue.*  [OWN.110] says the proof machine's store buffer is a FIFO: a hart's stores reach memory in
program order.  RVWMO itself is weaker: two stores of one hart to different addresses may reach memory in either
order unless a fence sits between them.  The FIFO is harmless for the theorem only if the replay never needs the
weaker order; P0(a) checked every store in the kernel and found that, apart from the `ip->ref` case above (which the
FIFO does not cause and option (a) above fixes), the FIFO is harmless — on the strength of a census of 1,331 store
sites plus a small argument about `acquire`'s text.  A buffer that orders stores only by address and by fences
needs no such census: progress then follows from the architecture's own rules.
*Tiny example.*  Hart A: `lk->cpu = me` (inside `acquire`), then `ip->ref++` — two unfenced stores.  FIFO: the
second may not land before the first.  RVWMO: either may land first.  Nothing in xv6 reads these two in a way that
tells the difference, but proving that is the census; with the RVWMO-shaped buffer there is nothing to prove.
*Terms.*  *FIFO*: first issued, first landed.  *Fence epoch*: the count of `fence rw,w`-like fences a hart has
executed; stores from an earlier epoch land before stores from a later one (rule 4).  *Same-address order*: two
stores of one hart to overlapping bytes land in program order (rule 1).  *Census*: a machine-checked list over the
kernel image.
*Options.*  **(a) FIFO (as ruled) + the census.**  Reads: "the proof machine is a little stronger than RVWMO on the
store side; the kernel never exercises the difference — checked site by site."  Machine STRONGER than RVWMO,
theorem FAITHFUL.  Cost: WCrel leaf 0.1–0.3k + `lk->cpu` reader lemma 0.2–0.4k + the (E1) case in `noStuckP`.
**(b) Per-address + fence-epoch buffer.**  Reads: "the proof machine's store side IS RVWMO's; every reordering the
architecture allows is a machine behaviour."  FAITHFUL on both counts.  Cost: +0.3–0.6k MachCSL (an epoch per
pending store, the landing guard, the release rule reads the fence), −0.3–0.7k Weak; neutral overall; one more case
in the riskiest interpretation lemma.  Recommendation: **(b)**, decided after P0(c) measures it (`landOk` is a
parameter in the spike); (a) if P0(c) shows the epoch case is expensive.

### Q-P-δ1 — what happens to the "stale silent AMO" rule ([OWN.105]) once the buffer exists?

*Plain-language issue.*  [OWN.105] gave the proof machine a rule letting a failed lock attempt read an older value
and leave no trace.  With the store buffer that rule is never needed: the "older value" is simply the current one,
because the release has not landed yet.  The rule can stay (dead) or go; going costs nothing extra if it goes in
the same edit that adds the buffer, because that edit re-proves every theorem the rule touches anyway.
*Tiny example.*  Hart 1 spins on lock `d` while hart 2's release of `d` sits in hart 2's buffer: with the buffer
the swap reads 1 at the top — an ordinary failed swap; δ1's rule would let it read 1 "from the past" instead.
*Terms.*  *Dead rule*: a machine behaviour no proof uses.  *Strict audit*: re-proving every registered theorem with
the assumption checker unchanged.  *P-M1*: the first MachCSL increment of route P (the state and the step rules).
*Options.*  **(a) Keep it dead with an extra side condition** ("no pending stores").  Reads: "the machine admits one
more harmless behaviour."  FAITHFUL; cost +0.3–0.8k of re-proof inside the P lane (every stale lemma gains a case).
**(b) Retire it after P** (cleanup row 8).  Reads: "the machine is the buffer model, nothing else."  FAITHFUL; cost
(a) + 0.3–0.6k + one more strict audit.  **(c) Retire it inside P-M1.**  Reads as (b).  FAITHFUL; cost ≈ 0 (deletions
in the same edit and audit); the three δ1 changes stay in history if ever wanted again.  Recommendation: **(c)**.

*Informational (no menu).*  (i) [OWN.108] ("pinned loads replayed STALE") is superseded by P: the gate holds back
the overwriting landing and the member reads the landed top — the ruling's per-site view/value datum is vacuous.
(ii) [OWN.111]'s premise holds: P replays the UART chain using only the fabric arm (R3); dropping the hart-side
(R1) later is a sized after-capstone item (A4, 1–2.5k), not a blocker — (R2)/(R2′) remain trusted platform text.
(iii) Q-6M-PTE (a) stays (progress, 0.3–0.6k).
