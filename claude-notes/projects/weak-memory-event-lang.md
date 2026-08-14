# The event-granular weak language — spike worklist

**Status (2026-08-14): SPIKE COMPLETE THROUGH S5, BOTH PARITY DEBTS PAID —
VERDICT: PASS (§ "Verdict").**  Design:
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
  per-node calibration point.  Since the F8 form change: ALSO the
  two-instruction composition (`ewp_ev_started_wait_seq`, the twin of
  `wwp_started_wait_seq`, `WeakEvStarted` §4) and the WHOLE-INSTRUCTION
  INSTANTIATION of the publisher at `main+0xb0`
  (`ewp_ev_started_set_at_main`, §5e) — every certification premise of a real
  kernel instruction discharged.
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
  `AK_ifetch` coherent one — AND THAT IS FINE, BECAUSE THE TEXT IS
  IMMUTABLE.  RESOLVED by a derived rule.**  MEASURED
  (`WeakEvStarted.ev_fetch_plain`, off the fetch request itself): the fetch
  at `main+0xb0` classifies as `(ak_coh, ak_latest, ak_sync) =
  (false, false, false)`, so the design's Decision 6 ("instruction fetch is
  declared coherent") does not describe what `riscv_step` emits and the
  general racy-load rule applies to it.  That cost every leaf one general
  rule application + one caller callback + one per-event `read_ok`
  justification, and was the single largest source of the S5 leaves' extra
  cost.  **The fix is `WeakEvLift.ewp_ev_fetch` (§5c): a DERIVED rule for
  reading NEVER-WRITTEN text.**  It consumes `etext_word` — the window form
  of the tree's own persistent kernel-text resource,
  `WeakInstr.wkernel_text` = a big-op of `wlat_pointsto a DfracDiscarded 0 b`
  (bridge: `WeakEvStarted.wkernel_text_etext_word`, one `acc_wf_byte` key
  conversion) — and concludes the fetch returns EXACTLY the certified word
  with **no caller callback, no `read_ok` obligation and no φ payment**:
    * the pinning lemma is proven once (`etext_byte_pin`): a byte whose
      latest write is the boot image has `latest_ts = 0`, hence
      `WeakBridge.pinned_read_unwritten`, hence `wbyte_ok_pinned` forces
      every admissible timestamp of a plain read to 0 and the value to the
      image's — so `bv_eq_of_bytes` gives `w' = w` and `tvs.*1 = replicate n 0`;
    * the φ payment is `WeakGhost.nv_ok_unwritten` at each byte whose floor
      moved (`coh_load_post_run_moved`, the load twin of the store lemma):
      a never-written byte owes nothing to any hart at any floor.
  **THE GAP, precisely.** The resource does NOT say "no message EVER writes
  this byte" as a claim about the log's future; it says "no message in the
  CURRENT log writes it", which is what a persistent `wlat_pointsto _ _ 0 _`
  means and is all the rule needs, because it is applied at the fetch
  event's own σ where the element is re-read.  A write to the text would
  have to consume the element's `DfracDiscarded` fraction and cannot — the
  discipline is enforced by the points-to, not by an extra invariant.  No
  "no-writes-ever" log-level fact exists in the weak tier and none is
  needed.
- **F8 — THE BATCHED INTERFACE'S EQUATION COULD NOT BE CLOSED AT A REAL
  INSTRUCTION IN THE FORM THE DESIGN SPECIFIED.  RESOLVED by the form
  change.**  `ewp_ev_batch` took `erun_silent n D rs m = (rs', m')`, and
  closing it requires NAMING `m'` — a Sail continuation.  Naming it means
  reading the VM's value back into a term, and readback of a closure
  normalises the whole rest of the instruction symbolically.  MEASURED:
  readback of one stretch's residual DID NOT FINISH IN 110 s, while the same
  computation projected to a number finishes in 0.1 s; and the cold-boot
  register file computes in 0.09 s but reads back in over 3 min.  The
  durable-notes recipe (compute-once-into-a-Definition + `vm_cast_no_check`)
  does not transfer, because it was written for VALUES and a monad residual
  is not one.  **The fix is `WeakEvLift` §3b**, and it changed no rule's
  content:
    * a CURSOR `ecur = regstate * M unit` with TOTAL steppers `esil n D`,
      `ecur_read v`, `ecur_write`, `ecur_bar`, `ecur_loop tick`.  A
      certification is a CHAIN OF APPLICATIONS
      (`esil n2 D (ecur_read v (esil n1 D x))`), never normalised;
    * `ewp_ev_batch` takes **no equation at all** — its successor is the
      unevaluated `esil n D x`;
    * TOTAL PROJECTIONS with SMALL outputs — `enode_tag` (a number),
      `eread_req_at n` / `ewrite_req_at n` (the request record, a value:
      pa, access kind, va, translation, tag), `ebar_at` (the barrier kind) —
      each per-site fact one `vm_cast_no_check` with a hand-written RHS;
    * FOUR ONCE-PROVEN INVERSIONS (`eread_req_at_inv` & co.) by which the
      rules match on the residual's head, exhibiting the continuation the
      projection hid.
  **AND ONE PROOF-ENGINEERING GOTCHA, MEASURED (durable):** a cursor equation
  must be discharged by `have H : … by reflexivity` and PASSED, never written
  as a bare `eq_refl` inside the application.  `reflexivity` calls
  CONVERSION, which unfolds the cursor's own definition, sees the same term
  and stops (0.003 s); a bare `eq_refl` leaves the problem to the
  ELABORATOR'S UNIFIER, which unfolds `esil` instead and starts LAZILY
  EVALUATING the stretch — 5.3 s for the second equation and unbounded (>100 s,
  killed) for the third.  Same statement, same proof term, different tactic.
- **F9 — the fused RMW's window is the one place the batching footprint leaks
  into a memory-event rule.**  The window's register writes happen inside the
  event, so `ewp_ev_rmw` must move the register authority in one ghost update
  and therefore takes a pure premise: every window the machine can take at that
  node is one the reflective stepper takes at the declared footprint.  Without
  it the rule is not merely harder — it is false (a window writing an unowned
  register cannot re-establish `gregs_interp`).

## S5 measurement matrix (RE-MEASURED 2026-08-14 after the F7/F8 fixes)

Machine: the shared box, single-file `coqc`, one variant per process.  Times
are `coqc -time` per-sentence sums attributed to the enclosing lemma (the
async `Qed` worker is not counted there; whole-file walls are `/usr/bin/time`).
**Both sides were re-measured in the same session** — the pre-fix table quoted
baselines from an earlier one, and they drift ~±20 %; the ratios below are
same-session.

### (a) BATCHED — the event-granular leaves (`iris/WeakEvStarted.v`)

| lemma | scope | time | lines |
|---|---|---|---|
| `ewp_ev_started_set` | publisher: whole `sw`, escrow set | 1.11 s | 105 |
| `ewp_ev_started_load` | subscriber: whole racy `lw`, escrow collapsed | 1.50 s | 119 |
| `ewp_ev_started_fence` | subscriber: whole `fence r,rw`, receipt cashed | 0.58 s | 62 |
| `ewp_ev_started_wait_seq` | the TWO-INSTRUCTION composition | 0.45 s | 77 |
| `ewp_ev_started_set_at_main` | the publisher AT `main+0xb0`, all premises | 2.87 s | 24 |
| **file total** | + §5 measurement + §6 calibration | **9.5 s wall, 1.18 GB, 912 lines** | |

Shared rules consumed (`iris/WeakEvLift.v`, 1812 lines, 11.5 s wall): the two
RAM rules `ewp_ev_store` 0.42 s / `ewp_ev_load` 0.59 s, **the derived fetch
`ewp_ev_fetch` 0.81 s**, the fused RMW `ewp_ev_rmw` 0.72 s, the batching core
`ewp_ev_sil_node` 0.60 s + `ewp_ev_sil_rtc` 0.07 s + `ewp_ev_batch` 0.005 s,
`ewp_ev_barrier` 0.29 s, and the five adapters `ewp_ev_seq_load` 0.43 /
`_fetch` 0.09 / `_store` 0.23 / `_barrier` 0.06 / `_ret` 0.04.

### (c) INSTRUCTION-ATOMIC originals (the same handshake, today's interface)

| lemma | file | time | lines |
|---|---|---|---|
| `wwp_started_set` | `WeakAcquire.v` | 0.70 s | 57 |
| `wwp_started_load` | `WkStartedLoad.v` | 1.64 s | 72 |
| `wwp_started_fence_gen` + `_r` | `WkStartedLoad.v` | 0.33 s | 32 |
| `wwp_started_wait_seq` (composition) | `WkStartedLoad.v` | 0.87 s | 58 |
| file walls | `WeakAcquire` 6.8 s, `WkStartedLoad` 5.1 s | | |

REUSED VERBATIM BY BOTH (not re-proved, not weakened): `WeakStarted`'s
σ-altitude escrow — `wstarted_set`, `wstarted_observe`, `wstarted_alloc`,
`wstarted_deliver_gen`, the one-shot lower bound.  That is the S4 header's
(F3)(d) confirmed at whole-function scale.

### PARITY VERDICT — TIME PARITY REACHED, LINES NOT

| pair | time ratio | line ratio |
|---|---|---|
| publisher (`set`) | 1.11 / 0.70 = **1.58×** | 105 / 57 = 1.84× |
| subscriber load | 1.50 / 1.64 = **0.91×** | 119 / 72 = 1.65× |
| subscriber fence | 0.58 / 0.33 = **1.76×** | 62 / 32 = 1.94× |
| the three together | 3.18 / 2.67 = **1.19×** | 286 / 161 = **1.78×** |
| + the composition | 3.63 / 3.53 = **1.03×** | 363 / 219 = **1.66×** |

**TIME: parity target (≤1.2×) MET** — 1.19× on the three leaves, 1.03× with
the composition, against 1.55× before the fixes.  The two payments are
independent and both landed: F7's derived fetch rule removed a callback and a
`read_ok` per instruction (and the fence leaf, which is pure fetch overhead
against a baseline with no memory content at all, still carries the worst
per-leaf ratio — 1.76× — exactly as predicted); F8's form change removed the
whole readback problem, and with it the only obstacle to the composition and
to instantiating a leaf at a real instruction.

**LINES: parity target NOT met, at 1.66–1.78×, and the residue is in the
STATEMENT, not the proof.**  Split (three leaves): statements 86 vs ~43 lines
(2.0×), proofs 200 vs 118 (1.7×).  The cause is structural and should be
quoted as such: an event-granular leaf ITEMISES its certification per event
(three cursor equations + three node projections + the per-node plain-read
facts + the text resource), where the instruction-atomic leaf takes ONE opaque
`wstep_cert`/`wracy_cert` premise.  The composition is the closest to parity
(1.33× lines) because both sides itemise there.  One cheap, unclaimed trim
remains: the triple `dev_addr … = false` / `ak_coh … = false` /
`ak_latest … = false` occurs at every read node and should be one named
`eplain_read` predicate — worth ~14 lines across the four leaves and a
better-named interface, not worth a re-measurement.

### (b) CALIBRATION — naive per-node vs batched (the anti-pattern)

`WeakEvStarted` §6, eight consecutive silent nodes, node facts as hypotheses in
BOTH (so only proof-side cost is measured):

| route | applications | time | lines |
|---|---|---|---|
| `calib_naive_8` (per-node rule ×8) | 8 | 0.198 s | 33 |
| `calib_batched_8` (`ewp_ev_batch` ×1) | 1 | 0.049 s | 8 |

~19 ms of proofmode per node, so ~5.6 s per real instruction (293 silent
nodes) against ~0.15 s for three batched stretches — **~37× on the proofmode
axis**.  And the reduction axis is worse than a ratio: the naive route needs
293 NAMED residuals where the batched needs ZERO, and F8 says a named residual
is not computable — so the per-node interface is infeasible, not merely slow.
The design's prohibition stands, with numbers under it.  (Under the F8 form
`calib_batched_8` takes no equation at all and is 8 lines.)

### (d) THE CONCRETE `vm_compute` INSTANTIATION (S4 gap 4 / F8, CLOSED)

At the REAL instruction — `main+0xb0`, `c.sw a4,0(a5)` = `0xc398`, xv6's
`started = 1` — over `ColdBoot.cold_regs` with `a5 = &started`, `a4 = 1`
(`WeakEvStarted` §5, every fact VM-cast and kernel-VM-rechecked at `Qed`):

| fact | value |
|---|---|
| boundary → fetch | **107 silent nodes** (`ev_len1`) |
| the fetch request | `MemRead`, width 2, at `main+0xb0` = 2147487534, `AK_explicit`/plain/normal ⇒ `(coh,latest,sync) = (false,false,false)` |
| fetch → store | **178 silent nodes** (`ev_len2`) |
| the store request | `MemWrite`, width 4, at `&started`, value `lock_one`, plain |
| store → `Ret` | **8 silent nodes** (`ev_len3`); the tail ends at `Ret` |
| whole instruction | 293 silent nodes, 2 memory events |
| **VM cost of stretch 1** | **0.143 s** (it forces the cold-boot file) |
| **VM cost through stretch 2** | **0.157 s** |
| **VM cost of the whole chain, to `Ret`** | **0.162 s** |
| readback of ONE request (the only readback left) | ≈0.4 s, once, into a `Definition` |
| the whole leaf instantiated at it (`ewp_ev_started_set_at_main`) | 2.87 s / 24 lines |

So the O(1)-per-site claim now holds on BOTH axes: **0.16 s of VM for the
entire three-stretch chain** (target was "well under 1 s per stretch"), and
the term axis is fixed because nothing is read back except a five-field
request record.  Two traps still recorded: the base register file must be the
machine's own (over `WpDecodeBridge.dregs` the same `riscv_step` traps — 141
nodes to `Ret` with no fetch, because a file with no PMA regions cannot
fetch), and `cold_regs` is fine to COMPUTE over but its 300-write readback is
not (>3 min, killed) — compute freely, never name the result.  The 2.87 s of
`ewp_ev_started_set_at_main` is Iris application, not VM: the VM inside it is
the 0.16 s above.

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

**THE SPIKE PASSES, FULL STOP.**  All three named fail criteria are cleared,
the S3 success criterion (`pf_violation_free_hart` from adequacy with ZERO
glue premises) is machine-checked, a whole function — both halves of the
`started` handshake — is re-proven at event granularity, the two halves
COMPOSE across an instruction boundary, and the publisher is INSTANTIATED at a
real kernel instruction with every certification premise discharged.
Everything is on the 5 rv64d sail axioms and nothing else (`Print Assumptions`
on `ewp_ev_started_set`, `_load`, `_fence`, `ewp_ev_started_set_at_main`,
`ewp_ev_fetch`, `ewp_ev_batch` and `ewp_ev_rmw`: `plat_term_write` + the
reservation quartet, seven times over; no `Admitted`, no new axiom).

**AND IT PASSES WITH TIME PARITY**: 1.19× the instruction-atomic leaves'
time on the three leaves, 1.03× with the composition (was 1.55×), after the
two debts were paid — F7's derived fetch rule and F8's form change.  It does
NOT reach line parity: 1.66–1.78×, and the residue is the certification's
PER-EVENT ITEMISATION in the statement (2.0× on statements, 1.7× on proofs),
which is what event granularity is.  Quote that as the price.

The premise ledger the architecture pivot was for is real: the event-granular
route needs NO `sail_shaped`, `sail_live`, `rv64d_live_residue`, `Hcq`,
`Hseip`, `Hpriv`, `cls_canonical`, `cone_liftable`, oracle stream, block cover
or hart restriction.

## What the post-spike plan owes

1. **~~THE INTERFACE FORM CHANGE (F8)~~ — DONE** (`WeakEvLift` §3b), and
   **~~A SPECIALISED FETCH RULE (F7)~~ — DONE** (`WeakEvLift` §5c).  Both are
   preconditions of any port and both are in.  What is left of them is one
   cheap trim (the `eplain_read` bundling, S5 matrix) and the durable gotcha
   about `have … by reflexivity` vs a bare `eq_refl` (finding F8).
2. **RETARGET M4 to the event interface** and port the weak leaves through the
   adapter: one `ewp_ev_seq_*` per memory event, `ewp_ev_seq_fetch` for the
   fetch (which needs only `etext_word` — bridge the function's
   `wkernel_text` window once per function).  Budget **~1.2× the
   instruction-atomic leaf time and ~1.7× the lines**, and expect the
   per-leaf pattern of §§1–3 verbatim: cursor equations by `have … by
   reflexivity`, node facts by `vm_cast_no_check`, nothing else.
3. **THE LAYER-1 GENERALISATION (S2) — PARTLY DONE, PARTLY REFUTED.**  The
   shared device component LANDED (fabric effort G1–G4,
   [`weak-memory-fabric.md`](weak-memory-fabric.md)): `WeakPromise.wpcfg`
   carries `pc_dev : D` and `pstep` moves it.  Two of the three reasons
   `epf_step` was still not an instance are now settled: the free message
   class is PINNED at fulfil time (G6a), and the PLIC hart index is a
   recorded cheap fix.  The third is **REFUTED**: the disk's DMA reads the
   flat memory, which is a `lat` (latest) read, and Layer 1's `pstep` must
   stay LOG-BLIND for the front-loading commutation and the cone replay to
   work at all (design note
   [`design/weak-memory-m6-robustness.md`](../design/weak-memory-m6-robustness.md)
   §10).  So the instantiation cannot be completed by generalizing `pstep`
   further; the disk arm's memory stays existential until the machine has
   DEVICE VIEWS (M5), and the residue is a reachability-inclusion premise
   ("the memory-free disk arm reaches nothing the flat-faithful one does
   not"), NOT a memory-blindness premise, which is refutable.  Read the
   fabric worklist's G6 section before attempting this again.
4. **RETIRE THE LIFT TREE** to `completed/` once the port lands: the bracket
   files (`WeakInterp`'s wrun-as-language-step, `WeakSailLTS`/`2`,
   `WeakSailComplete`, `WeakSailCone`, `WeakRobustCone`, `WeakComposeLang`),
   the shape towers, `WeakRetag`, the oracle machinery and both axiom-shape
   records.  `WeakStale`'s stale-memory mirror goes with them (the walk-bridge
   dissolves at event granularity).
5. **S6 (the 6c retarget note)** is still owed, and phase 2 of
   [`weak-memory-premises.md`](weak-memory-premises.md) proceeds unchanged —
   it is granularity-independent.
