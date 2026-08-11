# M6 — the store-reordering robustness theorem (worklist)

**Status (2026-08-11): planned, nothing landed.** Entry points: read
[`design/weak-memory.md`](../design/weak-memory.md) Decision 1 for the gap,
then [`design/weak-memory-m6-robustness.md`](../design/weak-memory-m6-robustness.md)
for the end-state composition and the Layer-1/Layer-2 split. This file is the
live plan: it settles the tee-up's two OPEN questions from the PARM sources
(§0), takes the decisions the tee-up left open (§1), and stages the work (§2).

PARM sources: `snu-sf/promising-arm` @ `10291375` (2022-09-01), read
2026-08-11. Cloned to a scratchpad (ephemeral) — re-fetch with
`git clone --depth 1 https://github.com/snu-sf/promising-arm.git`. All
`Promising.v` line numbers below are against that commit.

## 0. Questions settled from the PARM sources (2026-08-11)

- **Exclusive-conditional writes CAN be promised — the third store class is
  NOT free.** `Local.promise` (Promising.v:798) is unconditional and no
  promise rule inspects access kinds. What pins the walker's CAS is the
  FULFIL rule: fulfilling with `ex = true` requires
  `EX: exbank = Some eb ∧ (eb.loc = loc → Memory.exclusive tid loc eb.ts ts)`
  (Promising.v:884–886) — no other agent's write to the location in
  (LR-read ts, SC ts). Combined with the read half being `ak_latest`, an
  early-promoted A/D write-back's VALUE is a function of the coherence-latest
  PTE and its window admits no interposition — so the Layer-1 argument for
  arm (iii) is **commute-EARLIER** (early promotion ≡ running the walker
  earlier, itself a legal promise-free run), not delay-to-fulfilment.

- **§5's `interference_certify` tension: RESOLVED — the scenario's premise
  is false, and the mechanism is the lever Layer 1 needs.**
  `interference_certify` (CertifyProgressRiscV.v:1233) has
  `CERTIFY: certify tid (st, lc, mem)` in the OLD memory as a premise. The
  CS-store-promised-while-lock-free scenario never satisfies it, even
  thread-alone: on RISC-V a successful SC's RESULT carries the write's
  timestamp as its view (`RES: … ifc (ex && arch == riscv) ts`,
  Promising.v:902); the acquire loop BRANCHES on that result, so the
  timestamp lands in `vcap` (control view); `vcap` is a join component of
  every later write's `view_pre` (Promising.v:873–881); and fulfilment
  requires `EXT: view_pre < ts_promise` (Promising.v:883). A CS store
  promised before the acquire has `ts_promise < ts_amo` (the AMO write
  appends later), so `EXT` can never hold — the promise was uncertifiable
  BEFORE any interference arrived. Two more riscv-only pins of the same
  flavor: an acquire read joins its post-view into `vwn` (Promising.v:852–853),
  and an exclusive write's `view_pre` joins the exbank view
  (Promising.v:876–880).

  **Consequence — the robustness invariant, now concrete:** a certifiable
  promise's timestamp exceeds every timestamp its thread's remaining path to
  fulfilment can route into `view_pre` (`vwn` via acquires, `vcap` via
  SC-result-fed branches, the exbank view via exclusives). This is what
  Layer 1 gets to assume about promises that survive into a behavior, and it
  is exactly what makes the fenced arm (ii) work: a certifiable promise of a
  release-fenced store already has ALL the writer's pre-fence stores in the
  log below it (else `vwo ⊑ view_pre` meets a later append and `EXT` fails),
  so a reader that acquires from the early-read promise sees the complete
  deposit — early read ≡ early execution, the simulation commutes it.

  ⚠ Our machine DROPPED `vcap` with the rest of dependency tracking (design
  Decision 3), and D-M6-5 keeps it out of the native FULL machine too. The
  `vcap` arithmetic above is PARM-side background — it shows PARM pins even
  more promises than the native machine assumes — and the Layer-1 proof must
  make do with the surviving pins (`w_vwNew` via fence/acquire, the rmw
  exclusivity window); see D-M6-5's escalation rule.

- **The `pf_exec` skeleton is stronger than the tee-up recorded.**
  `Machine.state_exec` (Promising.v:1758) is per-thread
  `rtc state_step` against the SAME frozen memory with NO interleaving at
  all — after the front-loaded promise phase, threads are fully independent.
  Layer 1's simulation is therefore about SINGLE-thread runs over a frozen
  log, not about interleavings.

- **NEW CONSTRAINT the tee-up missed: the toolchain seam.** PARM is
  Coq 8.15 + sflib + hahn (~17k lines); this tree is Rocq 9.x. The published
  equivalence theorem cannot be `Require`d. See D-M6-3.

## 1. Decisions taken by this plan

- **D-M6-1: Layer-2 mechanism = (A), the ghost trail**, with a THIRD tag arm
  for exclusive/`ak_latest` stores (§0 shows arm (iii) is real). Rationale as
  in the tee-up: (B)'s side enumeration is exactly the "checked once,
  silently invalidated later" shape this project has been bitten by, and the
  tag rides infrastructure (`wlog_auth`) that already exists.
- **D-M6-2: the violation pattern is a STATE predicate** over
  (promise-free state, classification map), not a trace property — views
  only grow by reading, so "some agent read an owned-unpublished message
  early" is visible in the reader's per-byte view floor, and a state
  predicate is what the existing state-interpretation/adequacy machinery can
  export. Candidate in W2.
- **D-M6-3: restate the full-promising machine natively; take the PARM
  correspondence by inspection.** The full machine is defined in our tree as
  an extension of `WeakMem.v` (per-byte, dependency-free). The
  `[full ≡ axiomatic RVWMO]` leg of the composition is then a
  definitional-correspondence note — same epistemic category as the
  model↔hardware seam — NOT a machine-checked link. A Rocq-9 port of PARM is
  the recorded upgrade path, not undertaken now. (Originally "kept
  syntactically parallel to PARM's rules" — weakened by D-M6-5: the native
  machine drops PARM's register-view components, and the correspondence note
  argues containment, not parallelism.)
- **D-M6-4 (Nickolai, 2026-08-11): devices = the simple disk agent,
  uniformly.** M6 is stated over the harts plus the ONE disk agent, as one
  more agent of the same LTS — it may promise in the full machine (a
  superset of real device behavior, free direction), and its DMA stores fall
  under the lease/owned class in the simulation. No device special-casing in
  the Layer-1 statement; richer device memory models are deferred with M5.
- **D-M6-5 (reverses an earlier W1 bullet): the native full machine carries
  NO register views and NO `vcap`** — per-agent state = `wstate` + promise
  set, nothing else (the AMO/CAS stays ONE combined event carrying its
  exclusivity window inline, so no exbank either). Rationale: (1) POLARITY —
  removing join components from `view_pre` only lowers it, admitting MORE
  fulfilments, so the native full machine is WEAKER than PARM's: free for
  the hardware ⊆ native-full direction (Decision 3's argument applied to
  the full machine), and it makes the D-M6-3 correspondence a containment
  ("our `view_pre` is a lower bound of PARM's") instead of a parallelism.
  (2) The program abstraction stays an event-level LTS the Sail machine
  instantiates trivially; keeping `vcap` would drag PARM's register-view
  dataflow — a toy language — into the Layer-1 statement. (3) The pins the
  KERNEL's discipline actually needs survive: `w_vwNew` via release fences
  and acquires (the fenced arm's `EXT` argument), and the rmw event's
  exclusivity window (the `SCexcl` arm). The §0 `vcap` arithmetic stays as
  PARM-side background — it explains why PARM pins MORE than we assume —
  and Layer 1 must NOT rely on it. **Escalation rule: if the Layer-1
  simulation hits a case only `vcap`-pinning can close, STOP — that means
  the weakened machine's premise is genuinely too weak, and the fix (add
  the component, or strengthen Layer 2's classification) is a design
  decision, not a local workaround.**
- **D-M6-6 (2026-08-11, from the W3 recon — AMENDS D-M6-1): the Layer-2
  tagging is a FUNCTION of the machine state, not a ghost existential.**
  The recon ([`weak-memory-m6-w3-recon.md`](weak-memory-m6-w3-recon.md))
  established that trace coherence is a QUANTIFIER problem: `rtc
  erased_step` is prefix-closed, so a per-state pure φ exported at every
  reachable state already covers every intermediate state of every
  execution — but only if φ takes no `∃ τ` tagging (witnesses at two
  reachable states come from two unrelated adequacy instantiations).
  Mechanism (A) as originally stated ("adequacy exports: every message in
  the final log is tagged…") produces exactly that existential and would
  force a ~200-line in-tree adequacy variant.  Instead: (i) the CLASS
  becomes a message field `wm_ak` (the access kind is already a parameter
  of every pure store certificate; `wm_tid` is the precedent for an inert
  field); (ii) PUBLICATION becomes an inert `w_pub : nat` watermark in
  `wstate`, raised by release fences and `rl` stores, read by no rule —
  neither existing view component has the right polarity, and there is no
  fence leaf to emit a ghost flip at anyway; (iii) the export is a pure
  conjunct of `weak_state_interp` plus a three-line change in
  `WeakAdequacy.v`'s final continuation.  NO adequacy variant.  The name
  "ghost trail" survives only in the sense that the state interpretation
  must additionally REFLECT per-byte ownership to prove φ inductively —
  see the rewritten W3, which budgets that as its own item.

- **D-M6-7 (2026-08-11, after W1 slice 1 and W4 slice 1 landed with
  DIFFERENT LTSs): `WeakAxiomatic.exec` is the canonical promise-free
  execution object, and everything meets there by PROJECTION.**
  `WeakPromise.v` (abstract program LTS + promise sets, `lat` load kind,
  PARM-style rmw = readable + `excl_ok`) and `WeakAxiomatic.v` (concrete
  labels, no promise sets, `rmw_latest`) were written independently and
  differ exactly where they should: promises and the `lat` kind exist only
  on the full-machine side.  Do NOT rewrite either file to match the
  other.  Instead: W1's erasure bridge maps a fused-store, empty-promise
  `WeakPromise` run to an `exec_wf` execution (the rmw arm's
  readable + `excl_ok` + own-coherence collapses to `rmw_latest` — the
  `amo_latest_unique` dovetail; a `lat` load projects to a plain `LLoad`,
  the pinning dropped soundly), and W4's projection lemmas map
  `WeakLitmus.lstep` / `WeakInterp.wrun` runs likewise.  W2's Layer-1
  statement then relates `WeakPromise` behaviors to `exec_wf` executions —
  one common target, no parallel notions.

## 2. The staged worklist

### W1 — the full-promising machine, natively — **COMPLETE (2026-08-11)**

Dependency-free siblings of `WeakMem.v` (stdpp only), same abstraction
level (addresses `Z`, agents `nat`).  Four files, all axiom-free:
`WeakPromise.v` (machine + invariants), `WeakPromiseLitmus.v` (LB
reachable), `WeakPromiseFact.v` (factorization + per-agent state_exec),
`WeakPromiseBridge.v` (erasure bridge to `exec`, both directions).
Remaining cosmetics live in the owed-lifts batch under W4.

- [ ] Per-agent promise sets + `promise`/`fulfil` steps mirroring
      Promising.v's rules at BYTE granularity. Decide and record the
      mixed-size rule: a promise covers a byte range; fulfil must match the
      promise exactly (no partial fulfilment) — this is the "no crack for
      width mismatch" answer the tee-up asked for.
- [ ] Behaviors: runs whose final state has every promise set empty (the
      `Machine.exec` analog). Sanity inclusion: every promise-free execution
      is a behavior of the full machine.
- [x] **The erasure bridge LANDED, axiom-free, BOTH directions**
      (`WeakPromiseBridge.v`): `wp_pf_step` (the fused promise-free
      fragment — no arm mentions a promise set; COH/EXT by construction),
      its inclusion into the full machine (`wp_pf_behavior`, via the new
      `wpstep_rmw_now` fused derivation), the projection to D-M6-7's
      canonical object (`wp_pf_bridge : rtc wp_pf_run (wp_init img ps) c →
      ∃ E, exec_wf E ∧ … cfg_match c (final state)`), and the REVERSE
      (`exec_wf_pf_run`, under a `prog_free` LTS + agent-range premise).
      The dovetail closed as designed: `own_coh` (an agent's own writes
      never exceed its own coh floor) needed NO strengthening, and
      `pf_rmw_latest` derives `rmw_latest` from `read_ok` + `excl_ok` +
      `own_coh` — the `amo_latest_unique` story made formal.  Notes for
      W2: the state projection is RELATIONAL (`cfg_match`), not
      functional — `mstate.ms_ws` is a function while `pc_ags` is a list,
      and literal equality would need funext; and the two label types
      share constructor names (`LLoad`/…) — qualify when importing both.
- [x] **The factorization LANDED, axiom-free** (`WeakPromiseFact.v`): the
      full PARM-Thm-7.1 analog INCLUDING the per-agent decomposition.
      `wp_behavior_factor`: every lat-free-program behavior = a promise
      phase from init, then a state phase; `wp_state_exec`: the state
      phase = agent 0's whole run, then agent 1's, …, each against the
      frozen log — PARM's `Machine.state_exec` shape, no interleaving.
      Proof architecture worth reusing: the five state rules are
      repackaged ONCE as `wp_astep`/`astep_ok` (view-update function +
      deleted-promise option, both pinned by the label), so the swap
      lemma has one case instead of five and is proved equivalent to
      `wpstep`'s arms in both directions — hoist it into `WeakPromise.v`
      as the canonical presentation if slice 3 wants it.  Load-bearing
      points, confirmed: `ws_bounded` fires `writes_in_app_inv` for
      `readable` (the ONE place `cfg_wf`'s bounds matter); `prom_wf`
      gives `S (length log) ∉ prom` for the same-agent (∪/∖) commute;
      and `read_ok`'s `lat` conjunct is the ONLY side condition not
      preserved by log extension — the lat-free restriction is the
      violation surface, not a proof artifact, exactly as designed
      (`lat_free_prog` is the program-level premise; the lat-read
      commutation folds into W2's conditional simulation where φ pays
      for it).  Ergonomics for slice 3: `eapply` for `WPLoad` (`lat`
      absent from the conclusion); consider `Set Primitive Projections`
      on `wpcfg` to kill the `wpcfg_eta` lemma.
- [x] Litmus sanity: **LANDED, axiom-free** (`WeakPromiseLitmus.v`,
      `lb_weak_outcome_reachable`): the LB weak outcome r1 = r2 = 1 is a
      `wp_behavior` of the full machine (hart 1 reads hart 0's UNFULFILLED
      promise at ts 1; hart 0 fulfils last), while `WeakLitmus.lb_inv`
      proves it unreachable promise-free — the inclusion is strict.  The
      load-bearing observation from the proof: EXT over the D-M6-5 reduced
      `view_pre` is the SINGLE hinge — a non-acquire load leaves `w_vwNew`
      untouched (which is what admits LB), and an acquire or `fence r,rw`
      before the store would raise `w_vwNew` past the promise and kill
      EXT.  That is the fenced-class Layer-1 argument in miniature.
      W→W/MP-writer variant not done (cheap, optional).  Cleanup owed:
      hoist the proof's two local helpers (`read_ok_single` into
      `WeakPromise.v`, `load_post_run_single` into `WeakMem.v`) next time
      those files are touched — do NOT touch `WeakMem.v` mid-flight while
      sibling agents build against its `.vo`.

### W2 — the violation pattern + Layer 1 (`WeakRobust.v`)

DESIGN (2026-08-11, coordinator; the decomposition W1's artifacts make
possible).  At Layer 1 the classification and publication are
PARAMETERS — `cls : wmsg → store_class` and a monotone
`pub : cfg → nat → Prop` — so Layer 1 never depends on the D-M6-6
plumbing (`wm_ak`, `w_pub`); the Iris side instantiates them.  The
observation floor witness is `coh`: ANY foreign read or write of a byte
raises the foreign agent's `coh` past the message's timestamp (a plain
read raises `coh` but not `w_vrNew`), so `coh` is the tightest per-byte
floor that sees every observation.

- [x] Vocabulary + violation predicate + Layer-1 goal statement, compiling
      (`WeakRobust.v` slice 1): `store_class`, the violation predicate
      (an owned-UNPUBLISHED message by `i` whose bytes a foreign `coh`
      floor has reached), `violation_free` over pf runs, `mem_of` (the
      flat memory a run's log denotes), and `robust` — every lat-free
      `wp_behavior` is matched by a `wp_pf_run` with the same per-agent
      program states and the same flat memory.
- [x] **W2a step 1 — the traced state phase, LANDED axiom-free**
      (`WeakRobustTrace.v`): `aev`/`atrace`/`ptraces` with the fulfilled
      timestamp RECORDED per event (`ae_ts` = `astep_ok`'s `D`
      verbatim — the packaging was exactly right for traces), extraction
      AND replay (`astep_of_atrace` / `atrace_replay`),
      `wp_behavior_traced`, and the full fulfilment accounting
      (`wp_behavior_fulfil_once`: every authored log position is
      fulfilled exactly once in its author's trace — existence by
      constructive induction, uniqueness by strict promise-set
      decrease).  Hoist candidates for the owed batch: `wp_astep_inv`
      (the record-building inversion `wp_astep_shape` lacks),
      `astep_of_rtc_frozen` (rtc-level frame+frozen), `NoDup` folded
      into `wp_phases`.
- [ ] **W2a step 2 — the dependency graph (coordinator).** Over a traced
      behavior: events = (agent, trace index); D = per-agent trace order
      ∪ {fulfil(p) → read-of-(S p)} edges, with fulfil(p) located by
      `wp_behavior_fulfil_once`.  Prove: `pf_violation_free` + the three
      classes ⇒ D acyclic.  **New finding that simplifies the graph
      (2026-08-11, from the COH fulfil condition): an agent can NEVER
      read its OWN unfulfilled promise in a completed behavior** — the
      read raises its `coh` on the byte past the promise's timestamp,
      and the later fulfil requires `coh < ts`; contradiction.  So own
      reads of position p always sit trace-AFTER fulfil(p) (a lemma to
      prove in the graph file), rf edges never conflict with po, and
      every potential D-cycle is genuinely CROSS-agent — the LB shape.
      Per-class refutation of cycles — **CORRECTED 2026-08-11 after the
      infrastructure slice landed; the original fenced sketch below is
      WRONG and kept only as the record of the mistake.**  The original
      sketch said SCfenced cycles die because `fence rw,w` (pr = true)
      pins reads po-before the fenced store below its timestamp.
      COUNTEREXAMPLE: LB with the fence BEFORE the load on both harts
      (`fence rw,w; load x; store y` ∥ symmetric) — both stores are
      po-after a release fence, yet the full machine reaches
      r1 = r2 = 1 (nothing after the fence raises `w_vwNew`, so EXT
      passes), and RVWMO allows it (no load→store ppo without a
      dependency) while the promise-free machine excludes it
      (po ∪ rf cycle).  So "store po-after `fence rw,w`" does NOT make
      early promotion harmless: the pin only covers reads po-BEFORE the
      fence.  **The load-bearing premise is READER-side acquire
      discipline**: every cross-agent read of an SCfenced/SCexcl
      message is acquire-shaped — label `aq = true`, or followed by a
      pr∧sw fence (`fence r,rw`) strictly before the reader's next
      fulfil.  That is exactly the kernel's actual discipline (the
      `lw; fence r,rw` racy readers, the `amoswap.w.aq` locks) and it
      is Iris-checkable at the enumerated racy-read rules.  With it the
      argument UNIFIES: segment lemma S1 — a disciplined read of ts
      followed in the same trace by a fulfil of ts' forces ts < ts'
      (aq: `w_vwNew ⊔= vpost ≥ ts` directly, forwarding disabled by
      `fwd_view_aq`; fence: `w_vrOld ≥ ts` then the fence ships it into
      `w_vwNew`; EXT at the fulfil) — so the message timestamp strictly
      increases around any cycle whose cross rf edges are all
      disciplined; contradiction.  S1's fence arm needs one auxiliary
      invariant, `fwd_own`: a forward-bank entry always points to an
      OWN-authored log position (banks start empty; only own stores
      insert), so a FOREIGN read is never forwarded and `w_vrOld`
      really rises to ts.  SCowned cross edges are NOT covered by S1 —
      they are refuted by φ, and that refutation needs the pf prefix
      the W2b construction builds (φ speaks about pf RUNS), so
      **acyclicity-under-φ is not standalone: the owned arm folds into
      W2b's induction**, and the standalone theorem takes
      "every cross rf edge is disciplined" as its premise.
      `class_pins` from the infrastructure slice therefore concretizes
      to: cls-soundness (an SCexcl message's fulfil is an LRmw; an
      SCfenced message's readers are acquire-disciplined), leaving
      SCowned to φ.  Expect the acyclicity proof to be a per-class
      height/measure argument mixing timestamps (fenced/excl arms) with
      the violation contradiction (owned arm).  NOTE after W4 slice 2:
      D stays EVENT-level (a machine step is atomic in the pf
      interleaving — its bytes cannot split across the topological
      sort); that is fine because D has no co/fr edges, so
      `ev_rfe_co_fr_cyclic` does not apply to it.  But W2b's
      read-admissibility argument must handle a multi-byte load reading
      a MIX of fresh and stale timestamps — test any candidate
      simulation relation against exactly that witness's shape, and
      consider reusing `WeakAxiomatic2.evpre`/`opos` (a read's position
      = its timestamp ⊔ its pre-view) as the W2b view-relation
      vocabulary.
- [ ] **W2b — the construction.** Topologically sort D; build the pf run
      by induction over the sort, carrying: a timestamp permutation π
      (the pf log order is FULFILMENT order, which differs from gmo — an
      agent may fulfil out of promise order), value-exact read matching
      (each read returns the SAME byte values at π-mapped timestamps),
      and a per-agent view relation (expected shape: pf views bounded by
      the π-image of full-machine views; the exact direction is the
      first thing the proof will teach — record it here when it does).
      The `readable`-transport lemma under π is the crux of the crux.
- [ ] **W2c — observables + transport.** From W2b: same final flat
      memory + same program states; the reducibility/safety transport
      corollary in the form W5's composition wants.  Note the full
      machine is never `wpstep`-stuck (promising is always enabled), so
      the transported content is about observable states of completable
      behaviors, not raw stuckness — state it that way.
- [ ] Byte-granularity audit of the whole simulation: every case per
      byte; W1's exact-match fulfil rule is what keeps a promise/fulfil
      width mismatch out.

### W3 — Layer 2, the state-derived classification (D-M6-6)

Independent of W1–W2 once W2 fixes the violation predicate's exact shape;
the two field sweeps are mechanical M4-batch work.  The evidence and
file:line map for every item is
[`weak-memory-m6-w3-recon.md`](weak-memory-m6-w3-recon.md).

- [ ] `wm_ak` message-class field: add to `wmsg` (`WeakMem.v:48`), thread
      through `wwrite_msg`/`wwrite_post` (`WeakInterp.v:451,473`), the `Q`s
      naming `wwrite_msg` (`WeakInstr.v:648/659/674/677`,
      `WeakWord8.v:493-520`) and the six store leaves — the value at each
      leaf is a constant already written in its effect trace.  The walker
      CAS classifies `SCexcl` automatically (`ak_latest` on both halves).
- [ ] `w_pub` watermark field: add to `wstate` (inert — read by NO rule),
      raised by release fences and `rl` stores.  Touch list:
      `WeakMem.v` record literals + `ws_le` + `ws_bounded`,
      `WeakInterp.barrier_post`, `WeakViewMono.v`'s five `mono_nat`s.
      Semantics provably unchanged (nothing inspects it).
- [ ] The φ conjunct in `weak_state_interp` (`WeakGhost.v:458`) and the
      export: `weak_state_interp_export : weak_state_interp g -∗ ⌜φ g⌝`,
      consumed by a three-line change in `WeakAdequacy.v:225-227`.  φ =
      violation-freedom over (log, `wm_ak`, `published` via `w_pub`) — NOT
      a bare "everything is tagged", which rules out nothing.
- [ ] **The ownership reflection — the real cost, budgeted as its own
      item.**  To prove φ inductively the interpretation must know who
      owns which byte; today `wlat_interp` is an agreement with no owner
      or domain content.  Design a per-byte owner/hazard reflection minted
      from the exclusive `↦w{1}` at store time and consulted at read time;
      the racy-load rules (`WeakRacy.v`, `WkStartedLoad.v`) are where the
      obligation is DISCHARGED (the started/first setters are `SCfenced`,
      so their racy readers are exempt by class — verify, don't assume).
- [ ] Move the log-append ghost updates to the funnel chokepoint
      (`WeakInstr.wp_winstr:524` / `WeakFunnel.wwp_instr:615`, which
      already hold the append fact), DELETING the six per-leaf
      `wlog_update` calls rather than growing them.  Optional but pays for
      itself during the two sweeps above.
- [ ] During the sweeps, CONFIRM the tree-wide claim the pattern rests on:
      every `↦w`/ownership transfer is fence- or AMO-mediated (align
      `published` with the existing release-deposit timestamps —
      `WeakInstr.wwp_release_deposit`, `WeakFence.release_deposit` — not a
      parallel notion), and that the disk agent's DMA appends
      (`WeakExec.wp_wdisk_step`) get classes when M5 fills that rule in.

### W4 — the characterization lemma (slice 1 LANDED)

- [x] **Slice 1 landed, axiom-free** (`WeakAxiomatic.v`, ~1800 lines):
      the event-labelled LTS over `WeakMem`'s rules (`mstate`/`mstep`,
      executions as explicit (state list, step list) pairs so event
      identity is position-in-run), the relations (per-byte `rf`/`co`/`fr`,
      `po`, `gmo` = log order, timestamp-0 as a virtual init event), the
      ppo fragment (fence/acquire edges, publication via `pub_w`/`pub_r`
      with internal-rf excluded à la `rfi ∉ obs`), and
      `Theorem promise_free_sound : exec_wf E → axiomatic_ok E` — the two
      promise-free strengthenings (`ax_no_thin_air` = acyclic(po ∪ rf),
      `ax_po_ww_gmo`) plus per-byte coherence (a lexicographic
      (byte-timestamp, position) embedding), atomicity, and the local
      ordering axiom `ax_ord`.  The interim assumption is now a checkable
      axiomatic statement.
- [x] **Slice 2 LANDED except the completeness residue**
      (`WeakAxiomatic2.v`, axiom-free): the global memory order is a
      total order on OPERATIONS `mop := (byte, event)` — a read placed at
      its timestamp JOINED with its `load_vpre` (`evpre`; the naive
      "at-its-timestamp" placement is refuted by `load; fence r,r; load`
      reading backwards-in-time) — with totality/transitivity/
      irreflexivity, `ob ⊆ gmo_op`, the co and rf-interval
      characterizations all in `promise_free_gmo`; and
      `promise_free_ob_acyclic` with FULL `rf` (stronger than herd's
      rfe-only form).  **§7's event-level external axiom is FALSE —
      machine-checked** (`ev_rfe_co_fr_cyclic`): a two-byte load reading
      byte 0 fresh and byte 1 stale closes an rfe;fr;co cycle with no ppo
      edge, so per-byte OPERATIONS are forced, matching RVWMO's
      memory-operation granularity.  `ppo_op` gained a fourth arm (po
      into a write — free promise-free, subsumes every store-successor
      ppo rule) and the `ord_pr` arm excludes a fused RMW's written
      bytes (the fence publishes the read half; the operation sits at
      the write half).
- [ ] Completeness residue: the general replay construction and the
      SC-candidate class LANDED (`cand_reachable`,
      `sc_cand_reachable` — every SC behavior is promise-free
      reachable; residue = exactly the stale reads);
      `promise_free_complete` is stated in checkable form and needs ONE
      lemma: VIEW DOMINATION (every replayed view value is ≤ `opos` of
      an `ppo_op`-predecessor).  Key structural finding: this is NOT a
      corollary of the local `ax_ord` — fence delivery is transitive
      (a floor value is justified by an `ob`-PATH), so completeness
      genuinely needs the global axiom.  Estimated 600–900 lines, one
      conjunct per view component, forward bank fiddliest.
- [ ] Projection lemmas — the load-bearing missing link for composition:
      `WeakLitmus.lstep → exec_wf` (cheap: the arms match 1:1) and
      `WeakInterp.wrun → exec_wf` (moderate: multi-byte + oracle; note a
      pinned/ifetch `ak_latest` read projects to a plain `LLoad` since
      `latest_readable` — the pinning is dropped, sound for this
      direction).
- [ ] WeakMem/WeakPromise lemma lifts owed (ONE batch, when those files
      are next touched — not while sibling `.vo`s are in flight).  Into
      `WeakMem.v`: `load_post_run_coh`, `store_post_run_coh` (now used by
      TWO files — WeakAxiomatic and WeakPromiseBridge's `own_coh`),
      `store_post_run_vwOld`, `load_post_run_vrOld'`,
      `load_post_run_vrNew_aq`, `store_post_run_fwd_inv`,
      `load_post_run_single`, `msg_byte_range` (from
      `WeakPromiseBridge.v`), `load_post_fold_vrNew_aq_vpre`,
      `load_post_run_vrNew_aq_vpre`, `rd_ok_ts_bounded` (from
      `WeakAxiomatic2.v`); also lift `exec_ws_bounded` and `evpre` + its
      lemmas into `WeakAxiomatic.v`, and `wp_astep_inv` /
      `astep_of_rtc_frozen` into `WeakPromiseFact.v` (from
      `WeakRobustTrace.v`).  Into `WeakPromise.v`: `read_ok_single`,
      de-`Local` `read_ok_ts_bounded`, `wpstep_rmw_now` (next to
      `wpstep_store_now`), and consider hoisting `WeakPromiseFact`'s
      `wp_astep`/`astep_ok` as the canonical state-rule presentation +
      `Set Primitive Projections` on `wpcfg`.  Delete the local copies in
      the four consumer files when lifting.
- [ ] **Recorded polarity exception (report to design review):** RVWMO
      ppo rule 6 (`.rl` on the successor) is NOT enforced by the machine
      (`w_vRel` is inert for stores promise-free), so on that one axis the
      model is WEAKER than RVWMO — free for adequacy, currently vacuous
      (the kernel image contains no release store), but it breaks the
      clean "promise-free is strictly stronger" narrative; noted in
      `design/weak-memory.md`'s polarity paragraph.

### W5 — composition and retirement

- [ ] The final theorem: full-machine behaviors (completable prefixes, per
      the tee-up §2(a)) transported through Layer 1 (premise from Layer 2)
      to `weak_system_adequacy`'s promise-free reducibility; stated so the
      promise-free machine visibly becomes scaffolding.
- [ ] Final `Print Assumptions` diff: baseline axioms + MMIO-ordering +
      no-icache; the store-reordering assumption RETIRED, replaced by the
      D-M6-3 correspondence note at the PARM seam.
- [ ] Notes upkeep: fold outcomes back into the design files; move this file
      to `completed/` when done.

## 3. Order and parallelism

W1 → W2 → W5 are serial (each consumes the previous). W3 runs in parallel
once W2's vocabulary file is fixed, and its leaf batches parallelize like the
M4 sweep. W4 is fully parallel and cheap — start it first if an agent is
idle, since it de-risks the fallback. Do NOT write any Layer-1 simulation
before W1's factorization lands: the single-thread-over-frozen-log framing is
what keeps the proof from quantifying over interleavings.

## 4. Risks and open cruxes

- **The violation pattern's sufficiency is still the crux.** The W2
  candidate covers the three classes; the simulation proof is where hidden
  cases will surface. Named suspects to check early: DMA/device agents
  (`wm_tid = None` messages — decide whether M6 quantifies over device
  agents or is stated before M5's device views land, and record it), and
  ownership transfers that are not fence-shaped (W3's confirm box).
- **The trace-coherent export is RESOLVED by D-M6-6** (state-derived
  tagging + prefix closure; no adequacy variant).  The named risk in its
  place is W3's **ownership reflection**: the state interpretation must
  learn who owns which byte before φ can be maintained inductively, and
  that is a design problem, not a sweep.
- **Estimate shape:** W1+W2 are the research core with unbounded tail risk —
  fallback 1 (ship the interim theorem, unconditional for Ztso) stays
  shippable at every point, so nothing here blocks the rest of the tree.
  W3 is mechanical M4-batch-sized work; W4 is bounded and independent.
