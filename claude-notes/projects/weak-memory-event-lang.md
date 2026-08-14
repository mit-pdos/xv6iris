# The event-granular weak language — spike worklist

**Status (2026-08-14): SPIKE COMPLETE THROUGH S5 — VERDICT: PASS, with two
named debts (§ "Verdict").**  Design:
[`design/weak-memory-event-granular.md`](../design/weak-memory-event-granular.md).
S1–S5 are landed and machine-checked (`iris/WeakEvLang.v`, `WeakEvPf.v`,
`WeakEvAdequacy.v`, `WeakEvLift.v`, `WeakEvStarted.v`); S6 (the 6c retarget
note) is not started.  The superseded instruction-atomic machinery is retained
side by side for its failure record; do not delete any of it until the M4
retarget lands.

## Spike deliverables (each is a named artifact)

- **S1 — the language** (`iris/WeakEvLang.v`): DONE.  σ = `wgstate` verbatim;
  `ELoop`/`ECycle` (the monad rides in the expression); `EDisk` carries the pf
  disk agent's fields; fused RMW; store classes computed; no oracles;
  stuck-is-fine.
- **S2 — the correspondence** (`iris/WeakEvPf.v`): DONE, with the recorded
  FINDING that it cannot be stated against `WeakPromise.wpcfg` — the fabric is
  a THIRD shared component and `wpcfg` has only two.  The route taken is the
  fabric-shared pf machine `epf_step` over the language's own configuration;
  ⇐ is a projection, ⇒ a label exhibition, no simulation.
- **S3 — interp + adequacy** (`iris/WeakEvAdequacy.v`): DONE.  `state_interp`
  = `WeakGhost.weak_state_interp` VERBATIM (no new ghosts, no functor pair);
  `weak_ev_pf_violation_free` derives the success criterion with ZERO glue
  premises (four machine facts about a booted `wgstate` + the WP package).
- **S4 — the lifting rules** (`iris/WeakEvLift.v`): DONE, plus this session's
  three gaps: the FUSED-RMW rule (§6), the CERTIFICATION ADAPTER (§7: the
  barrier event rule + four `ewp_ev_seq_*` combinators), and the concrete
  `vm_compute` instantiation (below, in `WeakEvStarted` §5).
- **S5 — one whole-function proof** (`iris/WeakEvStarted.v`): DONE.  The
  `started` handshake, both halves, at the instruction-atomic originals' scope
  (`ewp_ev_started_set` / `ewp_ev_started_load` / `ewp_ev_started_fence`), plus
  the concrete measurement at the real kernel instruction and the naive-
  per-node calibration point.  NOT delivered: the two-instruction composition
  (the twin of `wwp_started_wait_seq`), blocked on the certification's FORM
  and not on content — chaining at the boundary quantifies over the tick, so
  the next instruction's certification must be supplied as a dependent family;
  debt #1 below removes that.  `WeakEvStarted` §4 records it.
- **S6 — the 6c retarget note**: NOT STARTED.

## Findings F1–F9 (F1–F5 from S4, F6–F9 new)

- **F1** the hart has no spurious arm (delivery is the PLIC thread's), so no
  rule needs a Löb; **F2** reducibility is the one honest partiality, per node
  rather than per instruction (no `sail_live`, no `rv64d_live_residue`);
  **F3** the frozen-log assumptions (`WeakRacy.wadm_down`'s
  `wm_log s2 = wm_log s`, `WeakInstr.wQ_load_w`'s log-quiet conjunct) are
  DELETED, not replaced; **F4** interference stability is the rules'
  statement, not a side condition; **F5** the one-event escrow access is
  strictly easier than the whole-instruction hold.
- **F6 — THE FUSED RMW IS NOT ATOMIC UNLESS THE PLAIN ARM IS GUARDED.**  S1's
  MemRead arm let an exclusive read take the PLAIN disjunct as well
  ("a bare exclusive read is an ordinary load"), so the two arms OVERLAPPED and
  no one-invariant-access acquire rule could be stated — the caller would have
  had to prove the instruction's remainder in the unfused case too.  Fixed in
  `WeakEvLang` by guarding the plain arm with `ak_latest = false`; the cost is
  that a bare LR with no fused SC is stuck, and xv6 executes none.
- **F7 — THE INSTRUCTION FETCH IS A PLAIN RAM READ IN THIS MODEL, not an
  `AK_ifetch` coherent one.**  MEASURED (`WeakEvStarted.ev_fetch_node`): the
  fetch request at `main+0xb0` classifies as `(ak_coh, ak_latest, ak_sync) =
  (false, false, false)`.  So the design's Decision 6 ("instruction fetch is
  declared coherent") does not describe what `riscv_step` emits: the fetch
  takes `ewp_ev_load` — the same rule a racy data load takes — and its text
  bytes need a per-event `read_ok` justification plus a PINNING conjunct
  ("every admissible read of the text returns the certified word") in place of
  `WeakBridge.pinned_read`.  This is the single largest source of the S5
  leaves' extra cost, because every instruction now has one memory event more
  than its instruction-atomic twin.
- **F8 — THE BATCHED INTERFACE'S EQUATION CANNOT BE CLOSED AT A REAL
  INSTRUCTION IN THE FORM THE DESIGN SPECIFIES.**  `ewp_ev_batch` takes
  `erun_silent n D rs m = (rs', m')`, and closing it requires NAMING `m'` — a
  Sail continuation.  Naming it means reading the VM's value back into a term,
  and readback of a closure normalises the whole rest of the instruction
  symbolically.  MEASURED: readback of one stretch's residual DID NOT FINISH
  IN 110 s, while the same computation projected to a number finishes in 0.1 s.
  The durable-notes recipe (compute-once-into-a-Definition + `vm_cast_no_check`)
  does not transfer, because it was written for VALUES and a monad residual is
  not one.  The prescribed form change — total projections plus unevaluated
  compositions, so no call site ever writes a residual down — is written out in
  `WeakEvStarted` §5e and is small; it changes no rule's CONTENT.
- **F9 — the fused RMW's window is the one place the batching footprint leaks
  into a memory-event rule.**  The window's register writes happen inside the
  event, so `ewp_ev_rmw` must move the register authority in one ghost update
  and therefore takes a pure premise: every window the machine can take at that
  node is one the reflective stepper takes at the declared footprint.  Without
  it the rule is not merely harder — it is false (a window writing an unowned
  register cannot re-establish `gregs_interp`).

## S5 measurement matrix

Machine: the shared box, single-file `coqc`, one variant per process.  Times
are `coqc -time` per-sentence sums attributed to the enclosing lemma (the
async `Qed` worker is not counted there; whole-file walls are `/usr/bin/time`).

### (a) BATCHED — the event-granular leaves (`iris/WeakEvStarted.v`)

| lemma | scope | time | lines |
|---|---|---|---|
| `ewp_ev_started_set` | publisher: whole `sw` instruction, escrow set | 1.41 s | 108 |
| `ewp_ev_started_load` | subscriber: whole racy `lw`, escrow collapsed | 1.94 s | 122 |
| `ewp_ev_started_fence` | subscriber: whole `fence r,rw`, receipt cashed | 0.45 s | 63 |
| **file total** | + §5 measurement + §6 calibration | **7.2 s wall, 774 MB, 897 lines** | |

Shared rules consumed (`iris/WeakEvLift.v`, 1322 lines, 10.2 s wall): the two
RAM rules `ewp_ev_store` 0.40 s / `ewp_ev_load` 0.59 s, the fused RMW
`ewp_ev_rmw` 0.77 s, the batching core `ewp_ev_sil_node` 0.49 s +
`ewp_ev_sil_rtc` 0.13 s + `ewp_ev_batch`, the adapter `ewp_ev_seq_load`
0.61 s / `_store` / `_barrier` / `_ret`, `ewp_ev_barrier` 0.24 s.

### (c) INSTRUCTION-ATOMIC originals (the same handshake, today's interface)

| lemma | file | time | lines |
|---|---|---|---|
| `wwp_started_set` | `WeakAcquire.v` | 0.58 s | 58 |
| `wwp_started_load` | `WkStartedLoad.v` | 1.70 s | 72 |
| `wwp_started_fence_gen` + `_r` | `WkStartedLoad.v` | 0.18 s | 33 |
| `wwp_started_wait_seq` (composition) | `WkStartedLoad.v` | 0.88 s | 59 |
| file walls | `WeakStarted` 4.35 s, `WkStartedLoad` 5.23 s, `WeakAcquire` 7.08 s | | |

REUSED VERBATIM BY BOTH (not re-proved, not weakened): `WeakStarted`'s
σ-altitude escrow — `wstarted_set` 0.44 s / 67 lines, `wstarted_observe`
0.51 s / 35 lines, `wstarted_alloc`, `wstarted_deliver_gen`, the one-shot lower
bound.  That is the S4 header's (F3)(d) confirmed at whole-function scale.

### PARITY VERDICT — NOT REACHED, AND THE GAP IS STRUCTURAL

| pair | time ratio | line ratio |
|---|---|---|
| publisher (`set`) | 1.41 / 0.58 = **2.4×** | 108 / 58 = 1.9× |
| subscriber load | 1.94 / 1.70 = **1.14×** | 122 / 72 = 1.7× |
| subscriber fence | 0.45 / 0.18 = **2.5×** | 63 / 33 = 1.9× |
| the three together | 3.80 / 2.46 = **1.55×** | 293 / 163 = **1.8×** |

Two of three leaves are above the 2× line the honesty protocol names, and the
aggregate is 1.55× time / 1.8× lines.  The cause is identified and is not
tactic slop: **every instruction has one memory event more than its
instruction-atomic twin, because the fetch is a memory event (F7)** — one extra
rule application, one extra caller callback (the text's `read_ok` + pinning),
one extra view transport per leaf.  The fence leaf shows it most starkly: its
instruction-atomic rule has NO memory content at all, and its event-granular
twin has a fetch.  Nothing in the measurement suggests the gap shrinks with
practice; it should be quoted as a per-leaf constant of ~1.5–2.5×, against
which the ledger deletions (below) are the payment.

### (b) CALIBRATION — naive per-node vs batched (the anti-pattern)

`WeakEvStarted` §6, eight consecutive silent nodes, node facts as hypotheses in
BOTH (so only proof-side cost is measured):

| route | applications | time | lines |
|---|---|---|---|
| `calib_naive_8` (per-node rule ×8) | 8 | 0.008 s | 34 |
| `calib_batched_8` (`ewp_ev_batch` ×1) | 1 | 0.002 s | 11 |

≈1 ms of proofmode per node, so ~0.3 s per real instruction (293 silent nodes)
against ~6 ms for three batched stretches — **~50× on the proofmode axis**.
And the reduction axis is worse than a ratio: the naive route needs 293 NAMED
residuals where the batched needs 3, and F8 says a named residual is not
computable — so the per-node interface is infeasible, not merely slow.  The
design's prohibition stands, with numbers under it.

### (d) THE CONCRETE `vm_compute` INSTANTIATION (S4 gap 4)

At the REAL instruction — `main+0xb0`, `c.sw a4,0(a5)` = `0xc398`, xv6's
`started = 1` — over `ColdBoot.cold_regs` with `a5 = &started`, `a4 = 1`
(`WeakEvStarted` §5, all five facts VM-cast and kernel-VM-rechecked at `Qed`):

| fact | value |
|---|---|
| boundary → fetch | **107 silent nodes** |
| the fetch event | `MemRead`, width 2, `(coh,latest,sync) = (false,false,false)` at `main+0xb0` |
| fetch → store | **178 silent nodes** |
| the store event | `MemWrite`, width 4, at `&started`, value 1, `(latest,sync) = (false,false)` |
| store → `Ret` | **8 silent nodes**; the tail ends at `Ret` |
| whole instruction | 293 silent nodes, 2 memory events |
| per-stretch VM cost | ~0.09–0.23 s; the whole file with all five casts: 7.2 s |

So the O(1)-per-site claim holds on the COMPUTATION axis and is REFUTED on the
TERM axis (F8).  Two traps recorded with it: the base register file must be the
machine's own (over `WpDecodeBridge.dregs` the same `riscv_step` traps — 141
nodes to `Ret` with no fetch, because a file with no PMA regions cannot fetch),
and `cold_regs` is fine to COMPUTE over (0.09 s) but its 300-write readback is
not (>3 min, killed) — compute freely, never name the result.

## Fail criteria — verdicts

1. **A leaf that cannot be stated interference-stably: NOT HIT.**  Three whole
   instructions are stated at their events' own σ; no rule mentions any other
   state; the two frozen-log assumptions are deleted with nothing in their
   place (F3/F4).
2. **An invariant spanning several events of one instruction: NOT HIT.**  The
   escrow is opened and closed at the single data event (strictly easier than
   today's whole-instruction hold), and the lock acquire stays one access
   because the RMW is fused — once the plain arm is guarded (F6).
3. **The correspondence failing to be definitional: NOT HIT AS STATED, but S2
   found the real obstruction next door.**  `erased_step` ≡ the pf run IS
   definitional against the FABRIC-SHARED machine `epf_step`; what does not
   exist is an instantiation of Layer 1's `WeakPromise.wpcfg`, whose three-field
   shape cannot carry a shared device fabric.  That is a Layer-1 generalisation,
   not a simulation, and it is debt #2 below.

## VERDICT

**THE SPIKE PASSES.**  All three named fail criteria are cleared, the S3
success criterion (`pf_violation_free_hart` from adequacy with ZERO glue
premises) is machine-checked, and a whole function — both halves of the
`started` handshake — is re-proven at event granularity on the 5 rv64d sail
axioms and nothing else (`Print Assumptions` on `ewp_ev_started_set`,
`ewp_ev_started_load`, `ewp_ev_started_fence`, `ewp_ev_rmw` and the two
measurement lemmas: `plat_term_write` + the reservation quartet, six times
over).  The premise ledger the architecture pivot was for is real: the
event-granular route needs NO `sail_shaped`, `sail_live`, `rv64d_live_residue`,
`Hcq`, `Hseip`, `Hpriv`, `cls_canonical`, `cone_liftable`, oracle stream, block
cover or hart restriction.

**It passes WITHOUT parity**: the leaves cost ~1.5× the time and ~1.8× the
lines of their instruction-atomic twins (2.4× / 2.5× on two of three), for the
structural reason F7 names.  That is the price, it is bounded and constant per
leaf, and it should be quoted honestly when the M4 retarget is scheduled.

## What the post-spike plan owes

1. **THE INTERFACE FORM CHANGE FIRST (F8), BEFORE ANY PORT.**  Restate
   `WeakEvLift` §7's combinators over total projections
   (`enode_tag`/`eread_facts`/`ewrite_facts`-shaped) and unevaluated
   compositions, so that no leaf ever names a residual monad.  Small, changes
   no rule's content, and without it every ported leaf hits the readback wall
   (`WeakEvStarted` §5e has the recipe).  Do this and re-do the (d) row of the
   matrix: the certification equations should then close at the real
   instruction in ~1 s.
2. **THE LAYER-1 GENERALISATION (S2).**  `WeakPromise.wpcfg` needs a shared
   device component (or `WeakRobustMain`'s Section `main` needs to be
   parametric in the configuration functor) before `WeakRobust.violation_hart`
   can be consumed at `epf_step`.  Until then the spike's capstone is stated at
   the fabric-shared machine, which is Layer 1's own predicate at the projected
   configuration — the statement is right, the instantiation is missing.
3. **RETARGET M4 to the event interface** and port the weak leaves through the
   adapter (one `ewp_ev_seq_*` per memory event, plus the fetch's callback per
   F7).  Budget 1.5–2.5× the instruction-atomic leaf cost.
4. **RETIRE THE LIFT TREE** to `completed/` once the port lands: the bracket
   files (`WeakInterp`'s wrun-as-language-step, `WeakSailLTS`/`2`,
   `WeakSailComplete`, `WeakSailCone`, `WeakRobustCone`, `WeakComposeLang`),
   the shape towers, `WeakRetag`, the oracle machinery and both axiom-shape
   records.  `WeakStale`'s stale-memory mirror goes with them (the walk-bridge
   dissolves at event granularity).
5. **S6 (the 6c retarget note)** is still owed, and phase 2 of
   [`weak-memory-premises.md`](weak-memory-premises.md) proceeds unchanged —
   it is granularity-independent.
