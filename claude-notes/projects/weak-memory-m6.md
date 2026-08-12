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

- **D-M6-8 (2026-08-12, coordinator — THE PREMISE-DISCHARGE SPLIT;
  found while designing W3's exports, supersedes the reader/writer
  "inert flag + φ conjunct" export items as the discharge mechanism
  for the trace-global premises).**  Layer 1's premises (rf_edges_ok,
  ee_ok, byte_ok) quantify over FULL-machine traces, but adequacy's φ
  covers only pf-reachable states — and a full-machine trace position
  po-after an early (pf-unsupported) read has a program state Iris
  never visits, so a φ-derived flag conjunct ("no agent fulfils while
  its discipline flag is set") CANNOT discharge them.  The way out is
  a three-way split of each premise's content:
  (a) MACHINE-side facts (EXT/COH/view arithmetic, `covered`,
  waw-cover's vwNew inequality) — pure statements about the traced
  wstates, premise-free or provable per-trace;
  (b) VALUE-INDEPENDENT SITE facts — the aq bit of the reading
  instruction, "the fence is the instruction immediately after the
  racy load / immediately before the release store", which depend
  only on the PC at the event, where minimal-cycle structure makes
  the pc supported: a minimal cycle visits each agent in one po
  segment (gpo shortcuts kill revisits), the segment head's po
  predecessors all lie in the acyclic ancestry U (pf-real by the
  subset sim), so the head's pc is Iris-covered, and the site's
  discipline instructions execute unconditionally before any
  value-dependent branch;
  (c) the residue — discipline of positions po-after an unsupported
  read, where only a static, value-independent code property can
  help.  DECISION: the final theorem carries (c) as an EXPLICIT,
  sharply-scoped static side condition on the kernel image (a
  per-site-checkable predicate over the enumerated racy/release
  sites; a checker tool is the recorded upgrade path), alongside the
  D-M6-3 correspondence note.  φ/Iris remains load-bearing ONLY for
  `pf_violation_free` (the SCowned arm), whose minimal-bad-edge use
  is sound as designed (the exhibit prefix is pf-real by
  construction).  This retires the store-reordering axiom into a
  machine-checked theorem plus auditable static side conditions —
  the honest form of the original goal.  W3's reader/writer
  discipline export items are re-scoped accordingly: the inert
  components stay (they make the site predicates statable) but the
  premise discharge is per-site/static, not a φ conjunct.

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
      SCowned to φ.  **SECOND REFINEMENT (2026-08-11, found integrating
      the landed measure theorem): `rf_disciplined` is too strong for
      OWNED-PUBLISHED reads.**  A critical-section read is a plain `ld`
      and the next store may follow fence-free inside the CS, so
      `disciplined` fails — yet the edge is harmless because the
      lock-acquire's `.aq` PRECEDED the read, raising `w_vwNew` above
      the release timestamp and hence above the message read
      (publication order): the read is COVERED — `ts ≤ w_vwNew` at the
      read's pre-state — and EXT alone pins every later fulfil, no
      fence needed.  The premise becomes `disciplined ∨ covered` per
      cross edge (covered's S1 case skips the fence machinery, straight
      to monotonicity + EXT); the Iris side discharges `covered` for
      owned-published reads from the pub/acquire story (the reader's
      view covers everything below the watermark it acquired).
      **STANDALONE ACYCLICITY LANDED, axiom-free**
      (`WeakRobustAcyc.v`): `fwd_own` (foreign reads never forwarded),
      S1 with the `edge_ok = disciplined ∨ covered` premise, and
      `gdep_acyclic_edges_ok` / `wp_behavior_gdep_acyclic` — dependency
      cycles impossible when every cross rf edge is
      disciplined-or-covered, by min-timestamp measure induction.  The
      same-event LRmw entry/exit branch is UNCONDITIONAL (the rmw's own
      COH conjunct on the post-read state gives the strict
      inequality).  The premise was sanity-checked against the
      fence-before-load LB counterexample (discipline genuinely fails
      there).  What remains of W2a is only what was folded into W2b:
      SCowned cross edges refuted by φ via the construction.  The Iris
      side owes `rf_edges_ok`: `disciplined` at the enumerated racy
      readers, `covered` at CS reads via the pub/acquire story.  NOTE after W4 slice 2:
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
- [x] **W2b slice 1 — the linearization backbone, LANDED axiom-free**
      (`WeakRobustLin.v`): event enumeration, Decision instances for
      every graph relation (bounded quantifiers — no classical axioms,
      no reflection substitutes), a REUSABLE generic toposort over any
      finite decidable acyclic relation, `gdep_toposort`, and
      `toposort_ind` — the induction interface the simulation consumes
      (process events in topological order, predecessors always done).
      Pairwise per-agent monotonicity provided; the filter-subsequence
      form is a short corollary if needed.
- [x] **W2b — the simulation LANDED, axiom-free (`WeakRobustSim.v`,
      1480 lines, 2026-08-12): `sim_full`, `sim_prefix` (the subset
      form over any `sub_ok` S), and `wp_behavior_robust` — the shape
      W5 chains `WeakRobustAcyc2`/`WeakRobustSer`'s wrappers into.
      Every case of the revised design closed as stated; finding (vi)
      realized literally (`gdep2_acyclic` is a per-theorem argument,
      no discipline premise anywhere).  Landing deltas recorded in the
      file: `pf_log = msg_at <$> fl` (lookup-fmap, not omap-induction);
      π factored through an abstract position list (`piL`, injective
      WITHOUT NoDup — disjoint ranges); `Hpred` is the only carried
      order fact; the cruxes factored as `read_ok_pf`/`excl_ok_pf`;
      two local promise-phase lemmas (`log_ne`, `promise_run_shape`)
      discharge the wrapper's premises.  (Design record below, kept.)**
      (design REVISED 2026-08-12 —
      the 08-11 pinned design was tested against the mixed fresh/stale
      witness as instructed and FAILED; two machine-level
      counterexamples found, both recorded here before building).

      **COUNTEREXAMPLE 1 — floor inversion (kills "any toposort of
      gdep").**  x@ts by j; x@t'' by m; y@t by k, with ts < t < t''.
      Reader i acquire-reads y@t, then plain-reads x@ts — behavior-legal
      (window (ts, t] is clean; t'' sits above the floor).  A toposort
      of gdep may process f(ts), f(t''), f(t), then i's reads (no gdep
      edges force otherwise): pf log [x@1, x@2, y@3], the acquire sets
      i's floor to 3, and the plain read of x@1 is BLOCKED by x@2 in
      (1, 3].  The π-inversion between an acquired message and a
      higher-timestamp stale write is fatal, so the graph handed to the
      sort must be EXTENDED (the E-edges below).

      **COUNTEREXAMPLE 2 — the post-fence store (kills "reader-side
      discipline suffices"; forces a NEW writer-side premise).**
      Writer: `fence rw,w; sd A; sd B` with promises giving
      ts(B) < ts(A).  EXT only checks `w_vwNew < ts`, and a fulfil
      raises `w_vwOld`, not `w_vwNew`, so both fulfils pass — the
      behavior is full-machine-real, and RVWMO allows it (A→B is bare
      po∩W×W, not ppo).  Reader acquire-reads B, then reads A's byte
      STALE (below ts(A)) — behavior-legal since ts(A) > ts(B) ≥ floor.
      Promise-free it is IMPOSSIBLE: the writer appends A before B, so
      acquiring B's position pulls A under the reader's floor.  Every
      cross read here is acquire-disciplined, so `rf_edges_ok` +
      reader-side class-soundness do NOT imply `robust`.  The missing
      premise is the DEPOSIT DISCIPLINE (S2 below) — exactly the
      kernel's actual shape (a publish/release store's fence covers ALL
      po-earlier stores; nothing is stored between the fence and the
      published store).

      **THE REVISED DESIGN**, in four pieces:

      (i) **View provenance (`WeakRobustProv.v`).**  Every wstate
      component of a trace prefix is `max` over a computable LEAF SET of
      message timestamps, and the pf run computes the SAME fold with
      leaves transported by π — stated once as: for σ with σ 0 = 0 and
      σ injective, each component of the σ-transported fold = max σ(the
      leaf set).  Mirrors the fwd bank (hit/miss transports because σ
      is injective; aq bypasses).  NOTE `load_post_at` raises `coh a`
      to max(vpost, t) — the coherence floor ABSORBS the read's whole
      pre-view, so coh's leaf set includes prior floor leaves, not just
      byte-a timestamps; the readable-transport below relies on leaves,
      never on "coh a only holds byte-a history".

      (ii) **The extended graph D⁺ = gdep ∪ E.**  For each read r
      (agent j, byte a, timestamp ts, behavior floor F = the leaf-max of
      max(load_vpre, coh a) at r): an edge f(t*) → f(t̂) for every leaf
      t* of r's floor and every byte-a write t̂ > F ("r stale-passes
      t̂"; such t̂ is automatically FOREIGN to j, since an own byte-a
      write above the own floor contradicts coh ⊆ floor).  Every E edge
      is timestamp-increasing (t* ≤ F < t̂).  OV := the set of E-targets
      (stale-passed writes).  With E in the sort, `readable` transports:
      window (π(ts), pf-floor]: byte-a writes ≤ ts sit ≤ π(ts) by
      per-byte co-monotonicity; (ts, F] is empty by the behavior's own
      readability; > F writes have π above every floor leaf by E —
      whether processed before or after r.  The rmw's excl_ok and the
      final mem_of equality transport from per-byte co-monotonicity
      alone.

      (iii) **Acyclicity of D⁺ — LANDED, axiom-free
      (`WeakRobustAcyc2.v`, 514 lines): `gdep2_acyclic_edges_ok` under
      ptraces_wf + fwd_own + rf_edges_ok + `ee_ok`, plus the behavior
      wrapper `wp_behavior_gdep2_acyclic`.**  Landing notes: the two
      milestone kinds collapsed into one `mile_mu` predicate (single
      gain lemma); the first-milestone decomposition returns a
      disjunction (a gE edge can be same-agent, so the no-milestone
      arm is killed by the gain applied to the milestone's own
      source); boundedness came free from the E edge's own
      `rd_floor < that` conjunct — `ptraces_ws_init`/`rd_floor_ws`
      are NOT premises.  `gE_ra` (byte hoisted out of `gE_at`'s
      existential) is the premise-facing spelling; `gmile` /
      `tc_gdep2_split` are reusable structural by-products.
      The walk design that landed (kept for the record):  The
      measure is a MILESTONE FLOOR µ, not the raw hop timestamp:
      after a cross-rf hop reading ts, µ := ts; after a gE hop from
      leaf t* out of read r, µ := F(r) (the read's whole floor — ≥ t*,
      so entering the gE hop from any leaf still increases µ).  Exit
      rules re-establishing "next milestone > µ":
        - cross-rf-read then po-later fulfil y: S1/edge_ok (landed).
        - gE-TARGET entry f(t̂) (edge floor F) then po-later cross-read
          or gE-source fulfil y: need y > F, by the NEW per-triple
          premise **ee_ok(r', t̂, y)**, a disjunction:
          (a) FENCE-COVER: a pw∧sw fence sits po-between f(t̂) and
          f(y), shipping t̂ ∈ w_vwOld into w_vwNew, so EXT gives
          y > t̂ > F — the release/publish sites (counterexample 2 is
          exactly a violation of this arm with no rescue);
          (b) WAW-COVER: the writer's w_vwNew at f(t̂)'s pre-state was
          already ≥ F — ownership transfer: before writing a byte a
          prior reader had a floor on, the writer synchronized past
          that reader's epoch (vwNew never decreases, and EXT at f(y)
          finishes); TWO WORKED REFUTATIONS pin this arm: the
          lock-epoch cycle (pre-acquire owned store t̂=100, acquire-AMO
          y=5 cross-read by waiters, gE return path through a second
          lock's reader) is killed by exactly this arithmetic — the L2
          handoff j'→w forces vwNew ≥ R_L2 > F(r') before f(t̂), and
          both L2 orders contradict; and
          (c) F = 0 / no real leaves: a racy stale-pass by a reader
          with an empty floor (the started spin: secondaries' floors
          are all 0 at the stale read) generates NO gE edges at all
          (t* = 0 is excluded — no fulfil of timestamp 0), so the
          started shape needs no premise.
      The earlier "S2/deposit" formulation is SUBSUMED by ee_ok arm
      (a); the earlier OPEN POINT is resolved by the µ-measure.  The
      Iris discharge per arm: (a) at release/publish sites (fence
      before the flag store covers all earlier fulfils), (b) from the
      ownership story (a WCplain write's byte came with a handoff that
      shipped every prior reader's floor), (c) free.  W3's
      writer-discipline export item should track ee_ok, not bare S2.

      (iv) **SCowned/φ via minimal bad edge.**  Per cross edge prove
      `edge_ok ∨ bad` (bad = owned-unpublished read).  If a bad edge
      exists, take a gdep-MINIMAL one: its ancestor closure is all-ok,
      hence sortable; sim that prefix; append the bad read — a pf run
      reaching a violating state, contradicting `pf_violation_free`.
      Consequences: the toposort/induction must run on a DOWNWARD-CLOSED
      all-ok subset (subset variant of `toposort_ind`), and the abstract
      `pub` parameter needs the property "pub only via processed
      release-events of the author" so ¬pub holds in the minimal prefix
      (the publishing fence is po-after f(ts) and outside the closure).

      Invariant carried along the (subset) `toposort_ind`, after
      processing `done`: (a) a pf config c' with
      `rtc wp_pf_run (wp_init img ps) c'`; (b) π: injective
      processing-order map from done's fulfilled timestamps to pf log
      positions, π(0) = 0; per-agent, done's events are a TRACE PREFIX
      (gpo forces it); (c) pf program states are the prefix endpoints';
      (d) pf wstates are definitionally the π-transported folds, with
      components = max π(leaves) by (i).

      **TWO MORE FINDINGS (2026-08-12, sharpening the file plan):**

      (v) **`robust` as stated is unprovable without a
      TIMESTAMP-OBLIVIOUSNESS premise on `pstep`.**  The pf witness
      steps the program with π-retimed labels (`LLoad`'s `tvs` carry
      timestamps), so a program that branches on a timestamp would
      diverge from the behavior's program states.  Add the premise
      "`pstep` is invariant under retiming a label's timestamps with
      values fixed" to `robust`; the Sail instantiation satisfies it
      trivially (programs see values only).

      (vi) **The simulation needs NO discipline premises — clean
      decoupling.**  The readable-transport closes from: the toposort
      order (E-edges order every floor-leaf's fulfil below every
      stale-passed write, processed or not), co-serialization
      (per-byte π-monotonicity, and "cross-author writes above an rmw
      are sorted after it" for excl_ok), leaf-fulfils ∈ done (rf/po
      downward closure), and the Prov correspondence.  Discipline
      (S1/S2/edge_ok/φ) is consumed ONLY by the acyclicity theorem.
      Moreover the sim should be stated over an arbitrary
      DOWNWARD-CLOSED (under gdep) toposortable event subset S — full
      S gives `robust`'s witness; the ancestor closure of a minimal
      bad (owned-unpublished) edge gives the φ-contradiction exhibit,
      with no separate mini-sim.

      **File plan:** `WeakRobustProv.v` (provenance) →
      `WeakRobustSer.v` (byte premises + co ⊆ tc(gdep)) →
      `WeakRobustOrd.v` (floor-leaf sets over trace prefixes, the E
      edges, D⁺ = gdep ∪ E, decidability, subset toposort) →
      `WeakRobustSim.v` (the subset sim; acyclicity of D⁺ taken as a
      hypothesis) ∥ `WeakRobustAcyc2.v` (acyclicity of D⁺ from the
      discipline premises — the remaining research risk) →
      `WeakRobustMain.v` (robust + bad-edge composition + W2c).
      **THE WRITE-SERIALIZATION LEMMA — a second pillar found while
      designing (2026-08-11): D has no co edges, and for UNCLASSIFIED
      programs that is fatal** — two agents' interleaved same-byte
      write pairs (x@5,y@2 by A po-ordered; y@3,x@4 by B po-ordered)
      form a realizable behavior whose co + po constraints are cyclic
      for ANY pf log, so no pf run reproduces its final memory.  The
      escape is the classification: for φ-disciplined programs every
      same-byte write pair is ALREADY tc(D)-connected in timestamp
      order — owned bytes pass through ownership-transfer chains
      (release→acquire rf edges), excl/lock words are chained by each
      AMO reading the previous release, started has a single writer —
      so π preserves co where it matters and final memory transports.
      State and prove `co ⊆ tc(D⁺)` (per byte, for classified traces;
      D⁺ = gdep ∪ E per the revised design above — the E edges only
      make this EASIER) as W2b's second lemma; its premises will
      sharpen what W3's class-soundness must export.  Proof route open:
      via the transfer chains (needs pub machinery) or operationally;
      record which closes.
- [ ] **W2c + the assembled Layer-1 theorem (`WeakRobustMain.v`) —
      DESIGN (2026-08-12, coordinator).**  Contents: (1) the per-edge
      premise weakened to `edge_ok ∨ bad` (bad = an owned-unpublished
      cross read, the shape φ refutes); (2) the case split: no bad
      edge → rf_edges_ok total → Acyc2 → full sim → `robust`'s
      conclusion; some bad edge → THE EXHIBIT: take U := the bad-free
      cone (events with no bad-edge target in their inclusive
      ancestry — downward-closed; all U-internal edges are edge_ok, so
      the restricted walk gives U-restricted acyclicity — instantiate
      WeakRobustLin's generic sort at R∩U² rather than editing
      anything), sim U via the subset sim, then append the minimal bad
      read (its po-prefix ⊆ U when its target is chosen with
      bad-target-free strict ancestry) — its pf step reaches a
      violating state, contradicting `pf_violation_free`.
      (2b) BAD'S EXACT SHAPE (pinned 2026-08-12): `bad(e1,e2)` :=
      cross grf ∧ the message's `wm_ak = WCplain` ∧ NO PUBLISHING
      EVENT of the author po-after f(ts_m) lies in ancestors(e2) —
      where "publishing event" is detected by the LABEL's rl bit or
      the message class WCrel (an rl-AMO raises `w_pub` while tagged
      WCexcl, so the class alone is not the raise condition).  The
      ancestry conjunct is what makes ¬pub hold at the exhibit state:
      processed events ⊆ ancestors(e2), the author's pf `w_pub` is
      the max over π of its processed raises, and author-po order
      transports through π — no processed po-later raise ⇒ π-w_pub
      below π(ts_m).  The third case (publish-ancestor via a third
      party with an uncovered reader) is neither edge_ok nor bad —
      it is claimed not to occur in the kernel and sits inside the
      edge_ok premise's discharge obligations.  The appended bad
      read's own pf-admissibility runs on the sim's readable crux
      verbatim (its E-edges connect U events and the U-sort orders
      them; multi-byte reads need all bytes' sources in U — they are,
      by rf-closure).
      (3) THE HONEST RESIDUE: a "bad SCC" — bad edges lying on a
      mutual-reachability cycle, i.e. spontaneously mutually-justified
      owned-read LB — admits no minimal bad target and no exhibit
      (its events' pf-realization is circular and its message never
      enters the pf log).  The theorem therefore carries the premise
      **`bad_wf`: bad-edge targets are gdep2-well-founded (no bad
      SCC)** — same epistemic category as D-M6-8's static residue,
      and the same justification: a bad SCC is exactly the
      thin-air-owned shape the kernel's discipline excludes.
      (4) W2c proper: the transport corollary is `sim_full`'s
      conclusion (same prog states + same flat memory) restated over
      completable prefixes for W5; the full machine is never
      wpstep-stuck, so state it about observables of completable
      behaviors, not stuckness.
      NOTE for the sim's premise plumbing when building Main: the
      subset sim's `writes_fulfilled` use must be checked — for a
      cone U it holds in the needed form (read sources of U-events lie
      in U); if the landed sim consumed the global form, weaken its
      hypothesis to the read-sources form.
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
- [ ] `w_pub` watermark field — **SEMANTICS REVISED (2026-08-12, from
      the W2b design work; supersedes "raised by release fences")**.
      Two inert `wstate` fields: `w_relp : bool` (pending release — SET
      by a pw∧sw fence, CLEARED by the agent's next store) and
      `w_pub : nat` (raised to the store's own timestamp at a store
      taken with `w_relp` set, and at an `rl` store).  The point: the
      RISC-V release idiom is `fence rw,w; sd flag`, and the FLAG store
      is the publication — EXT at that store forces every po-earlier
      store's timestamp below it (the fence shipped `w_vwOld` into
      `w_vwNew`), so `published p := S p ≤ w_pub(author)` covers
      exactly the deposit AND the flag store itself.  Raising `w_pub`
      at the fence (the old plan) covers only the deposit and leaves
      the flag store — the very message racy readers read — forever
      unpublished, making φ false at every racy read.  Consequence for
      the class: `wm_ak` is COMPUTED at append as
      WCexcl (ak_latest) / WCrel (`w_relp` set, or `rl`) / WCplain —
      fully machine-syntactic, resolving the recon's "plain store ≠
      owned store" caveat: SCfenced ≐ WCrel, SCowned ≐ WCplain, and the
      Iris side's job reduces to φ (no foreign floor reaches a
      WCplain-unpublished message), discharged because in the verified
      kernel every racy-publish site fences immediately before its
      store (making it WCrel) while WCplain stores are exactly the
      `↦w{1}`-owned ones.  Touch list unchanged plus the `w_relp`
      clear-on-store in `store_post`.  Semantics provably unchanged
      (nothing reads either field).
- [ ] The φ conjunct in `weak_state_interp` (`WeakGhost.v:458`) and the
      export: `weak_state_interp_export : weak_state_interp g -∗ ⌜φ g⌝`,
      consumed by a three-line change in `WeakAdequacy.v:225-227`.  φ =
      violation-freedom over (log, `wm_ak`, `published` via `w_pub`) — NOT
      a bare "everything is tagged", which rules out nothing.
- [ ] **The ownership reflection — the real cost, budgeted as its own
      item.  DESIGN SKETCH (2026-08-12):** φ's induction needs the
      interp conjunct "every unpublished WCplain message's bytes are
      hazard-marked to their author", via (1) a per-byte HAZARD ghost
      minted by the owned-store leaf (which holds `↦w{1}` anyway) and
      cleared by the release/publish leaf (whose fence+EXT math shows
      the author's WCplain positions land ≤ the new `w_pub`); (2) a
      per-byte DISCIPLINE map (BDOwned/BDSync): WCplain stores only at
      BDOwned bytes, racy-load rules only at BDSync bytes, BDSync
      stores always WCrel/WCexcl; (3) the fragment-load rule excludes
      foreign hazards through the points-to itself (fold the
      hazard-freedom into `↦w`'s definition so fractional arithmetic
      refutes a foreign unpublished-owned message on a byte anyone
      else can read).  Violation-freedom then closes per rule: a load
      raises `coh` only on the bytes it reads; each read is
      fragment-backed (hazard-free byte) or racy (BDSync byte, no
      WCplain messages at all).  The racy-load rules (`WeakRacy.v`,
      `WkStartedLoad.v`) are where the obligation is DISCHARGED (the
      started/first setters are WCrel by the `w_relp` rule — verify,
      don't assume).
- [ ] **The WRITER-discipline (S2/deposit) export — NEW, forced by
      W2b counterexample 2.**  The per-agent inert component records
      "an OV-class store since the last pw∧sw fence"; the exported φ
      conjunct is S2's premise (every publish/release-class store is
      fence-separated from ALL po-earlier stores).  Kernel-true at
      every enumerated release/publish site (`fence rw,w` immediately
      before the flag store; nothing stored between).  Design the
      component together with `w_pub` and the reader flag — all three
      ride the same `wstate` sweep.
- [ ] **The reader-discipline export** (same D-M6-6 pattern, one more
      inert component; see design §4b): a per-agent flag/watermark set by
      a PLAIN read of a classified foreign message, cleared by an acquire
      fence (`pr∧sw`) or an `.aq` read, with the exported φ conjunct
      "no agent fulfils while its flag is set".  Discharged in Iris
      because the enumerated racy readers are verified instruction
      sequences that pass through the fence leaf before any store leaf.
      This is what feeds W2a's `disciplined` premise
      (`WeakRobustAcyc.v`); design the exact component shape together
      with `w_pub` since both ride the same `wstate` sweep.
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
- [x] **Completeness LANDED in corrected form, with the effort's THIRD
      machine-checked refutation** (`WeakAxiomatic3.v`, 2026-08-12,
      axiom-free): §9(1)'s `promise_free_complete` and the
      view-domination lemma are both FALSE as stated
      (`promise_free_complete_false`, `view_domination_false`) — a
      3-step no-fence witness where an `rl` store feeds `w_vRel` into a
      later acquire's pre-view: the machine orders release→acquire
      UNCONDITIONALLY while the modelled ppo fragment omits RVWMO rule
      7 entirely, so the machine is stronger than the modelled axioms —
      free for soundness, fatal for completeness.  The corrected
      theorem `promise_free_complete_clean` closes under two added
      premises: `cand_rl_free` (no release store — vacuous for the
      kernel image; the alternative fix, adding rule-7 rel→acq edges to
      `ppo_op`, is noted for a future refinement) and `cand_pub_clean`
      (reads acquire or externally sourced — never forwarded).
      Non-vacuity is itself a theorem (`ce_rl_stale_reachable`: a
      genuinely stale read outside the SC fragment is reachable BY the
      theorem).  Two structural surprises, both recorded in-file:
      domination is carried as `frdom_b` directly (per-predecessor
      `opos` bounds cannot close the cycle), and **`ob`-acyclicity is
      never used** — `promise_free_complete_local` needs only the four
      local axioms, because `fence_between`/`acq_po` are monotone in
      the target, so chained fence delivery collapses to a single `ord`
      edge; the slice-2 prediction was wrong in our favor.  Honest
      residue: the second (forwarding-path) leak §14(1) is argued but
      not mechanized (~150 lines of §13 generalization); the §5
      `maxcl` upper-bound fold lemmas are owed to the WeakMem lift
      batch, and §12's finding that `cand_values` alone buys five of
      `axiomatic_ok`'s eight conjuncts is worth reusing.
- [x] **Projection lemmas LANDED, both axiom-free (2026-08-12).**
      `WeakLitmusProj.v` (277 lines): one `lstep` = exactly one `mstep`
      (no silent arm), `lstep_exec_wf` + the `_sb` sanity corollary
      fitting the litmus configs verbatim; the AMO arm's atomicity
      conjunct IS `rmw_latest` unfolded, no own_coh dovetail needed.
      `WeakInterpProj.v` (409 lines): `wrun_exec_wf` over
      `rtc (wstep i)` with `ws_match`/`proj_ext` packaging.  THREE
      deltas that matter downstream: (1) NEW PREMISE `nz_writes` (no
      zero-width writes — an n=0 append grows the log with an empty
      message no `mstep` can mirror; vacuous for real code, a caller
      obligation in W5); (2) **AMOs project as separate LLoad+LStore —
      the atomicity link is dropped** because the model emits the two
      halves as separate outcomes; sound for exec_wf but the W5
      composition needs the FUSED LRmw (D-M6-5), so W5's event-level
      Sail LTS must bracket exclusive-read…conditional-write into one
      label (the fix point is there, not in this file); (3) coherent
      (ak_coh) reads are silent (dead for rv64d anyway).  Env note:
      `by etrans` fails under this stdpp/ssreflect combo — use
      `etrans; [exact H1|exact H2]`.
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

DESIGN (2026-08-12, coordinator).  The seam between `wp_behavior`
(abstract per-agent LTS) and the real machine is an EVENT-LEVEL LTS the
Sail machine instantiates (exactly D-M6-5's rationale (2)):

- **`WeakSailLTS.v`** — `P_sail` := the residual instruction monad +
  register state (the intra-instruction continuation); `pstep_sail`
  mirrors `wrun`'s arms 1:1, memory outcomes emitting the label, all
  others `LSilent`.  Prove: lat-freedom (rv64d never emits
  AK_ifetch/AK_ttw — the W3 recon's finding (1)), TIMESTAMP-OBLIVIOUSNESS
  (labels' timestamps are not consumed by the continuation — programs
  see values only), and the BRACKETING lemmas: one `WeakLang` prim_step
  ⇔ a completed `pstep_sail` event sequence, both directions.
- **φ transport across bracketing**: adequacy exports φ at INSTRUCTION
  boundaries; the violation predicate is needed at EVENT granularity.
  Sound because a mid-instruction violation PERSISTS to the boundary:
  within one hart's instruction only that hart steps (`wrun` is
  thread-local), floors only grow, and other authors' `w_pub` cannot
  move — so `pf_violation_free` at event granularity follows from the
  boundary export.
- **THE DEVICE SEAM — RESOLVED (2026-08-12): it is the EXISTING
  MMIO-ordering assumption, not new machinery.**  `wpcfg` has no device
  component while the real machine has shared MMIO state as a second
  channel, and the sim's changed interleaving does not literally
  preserve cross-hart device-access order (informally it does — device
  accesses sit in lock CSs whose handoffs are rf-chained).  But the
  final-footprint plan (the W5 Print Assumptions item below) ALWAYS
  kept "MMIO-ordering" as a retained axiom — so scope the composition
  to harts + the disk agent over the log, with each hart's MMIO-read
  responses absorbed as a per-behavior ORACLE STREAM inside the
  abstract program state (P_sail carries the stream; device reads
  consume it silently, device writes are silent), and let the retained
  MMIO-ordering assumption cover the stream-run ↔ real-device-run
  correspondence in BOTH uses (the behavior factoring and the
  φ/`pf_violation_free` transport for exhibit prefixes).  φ itself is
  device-oblivious (device arms touch neither log nor ws), which is
  what makes the transport well-posed.  Do not build a device-aware
  full machine.

- [ ] The final theorem: full-machine behaviors (completable prefixes, per
      the tee-up §2(a)) transported through Layer 1 (premise from Layer 2)
      to `weak_system_adequacy`'s promise-free reducibility; stated so the
      promise-free machine visibly becomes scaffolding.
- [x] **`WeakSailLTS.v` LANDED (977 lines, 2026-08-12):** `psail`/
      `sail_step` (a `Definition` by match, mirroring `wrun`'s
      dependent-outcome idiom — an Inductive would fight the outcome
      types), the fused-RMW arm with a GENERAL silent prefix
      (`silent_run`), fence.tso split via a parked `sp_fence` that
      gates every arm, `sail_lat_free` + `sail_ts_oblivious(_rmw)` by
      construction, and the ⇒ bracket against `wp_pf_step`
      (`wrun_sail_bracket` / `sail_instr_bracket(_single)`) under
      `sail_shaped` (= no coherent reads + nz write widths + AMO
      pairing; dead-arm exclusions for rv64d).  Only
      `sail_instr_bracket` carries rv64d's baseline axioms (via
      `riscv_step`); everything else closed.  Scoped out and recorded
      in its header: the ⇐ direction (composition needs only ⇒; ⇐
      would need silent-prefix determinism) and the
      `wprim_step`/`wgstate` multi-hart lift (composition file's
      job).
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
