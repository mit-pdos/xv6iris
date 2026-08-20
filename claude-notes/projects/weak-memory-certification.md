# The certification route (D8 / E1 / L2′) — worklist

**S6 RAN AND THE GATE IS OPEN (2026-08-20): GO on this route.**  The
two-hart L2′ paper exercise is
[`../design/weak-memory-tier2-s6.md`](../design/weak-memory-tier2-s6.md) —
read it FIRST: it carries the full edge-inventory table (every kill named
M/φ/lock-protocol, none in C6), the two structural findings that reshape
the plan (F1: the `cand` presentation cannot express rule-14 violations,
so tier 2 needs a graph-presentation front-end for a declared **RVWMO⁻**
— RVWMO minus ppo 6/9–13, which only strengthens the final theorem and
dissolves the D-8 dependency-alphabet obstacle; F3: ONE new export, the
lock-word value protocol as a `weak_state_interp` ghost — the φ mechanism
— because `wlock_inv` is a namespace invariant adequacy cannot see), the
finding that §5's `w_rdw`/`w_lock` are NOT needed, the route-B fallback
trigger, and the revised staging **T2-0 … T2-6** that supersedes this
file's bare item list as the execution order.

**T2-0 LANDED (2026-08-20): the lock-word protocol export** — `wcds`
gains `WLock (base) (n0)` whose `wcds_ok` arm is `wcds_clean ∧ wlp_at`
(the clean half is FORCED: the suffix protocol says nothing about the
pre-registration history where `initlock`'s plain store sits, and φ's
`nv_ok` must still be paid); `wlock_inv` holds the new `wlat4L` bundle
(`n0` EXISTENTIAL inside it, so every downstream lock-client statement
is textually unchanged); `wlock_alloc` performs the C→WLock registration
flip; both lock cores store through `wcds_ok_store_lock`; the export is
`WeakGhost.wlock_regd` (a persistent invariant + accessor — nothing
discarded is minted; a `DfracDiscarded` cds copy would freeze the byte)
consumed by **`weak_ev_adequacy_lockproto`**: at every reachable σ,
`∃ n0, wlp_at (wglog σ) a base n0`.  On the 5 rv64d axioms.  TWO
DEVIATIONS THAT BIND T2-5: (i) the release arm of `wlock_shaped` is
`wm_ak ≠ WCplain ∧ data = zero`, NOT `= WCrel` (`wQ_store_w` leaves the
class existential) — so the trace-side `win_excl` derivation must take
the unlock's COVERAGE from the trace's fence (C4's
`covered_of_release_chain`), never from the message class, which is what
it did anyway; (ii) `wlock_regd` is per lock word — if T2-5 wants a
family at once, upgrade it to a finite set of `(base, N)` pairs rather
than adding a registry ghost (rejected: it reopens the ~50-site
`weak_state_interp` reassembly).

**T2-1 slice 1 LANDED (2026-08-20): `iris/WeakRvwmoGraph.v`** — the
RVWMO⁻ herd-style presentation (per-agent label lists; `gx_gmo` as DATA,
so stores can be early; read `ts` entries reinterpreted as gmo-write
indices, which makes `graph_of_cand` the identity on labels), the model
`rvwmo_minus_consistent` (gwf ∧ ppo⁻⊆gmo ∧ load-value with the
po-forwarding disjunct ∧ atomicity; ppo⁻ = rules 1–5, 7 only), and the
NON-COLLAPSE WITNESS `lb_graph_consistent` (the four-event LB execution
is RVWMO⁻-consistent — machine-checked proof that the declared model
admits exactly what sRVWMO forbids, so the tier-2 gap is real; Closed
under the global context).  **T2-1b owed, and OFF THE
CRITICAL PATH** (scoping finding, 2026-08-20): the safety chain consumes
only the graph→cand direction (T2-1c); cand→graph consistency transfer
serves the tier-2 EQUALITY statement only.  And it is NOT the easy
direction it looks: `graph_of_cand`'s trace-order gmo placement violates
`gload_value`'s co-maximality for STALE reads (a cand read of old `t`
sits trace-after newer same-byte writes), and the obvious repair — place
each read at its read-timestamp — breaks acquire ordering ACROSS bytes
(acquire x@t=5 then read y@t=2 is machine-legal but by-ts placement
inverts them against ppo rule 5).  Both translation directions are
genuine per-event scheduling arguments; expect interval/topological
placement, not a projection.  **T2-1c owed** (critical path): the
rule-14 linearization (graph → same-log cand) and the store-dep fragment
(`gx_deps`, per the S6 F2 caveat).  DESIGN WORKED OUT (2026-08-20, to
spec the build):
  - THE EXTENSION ORDER: R := po ∪ gmo|W ∪ rf-placement (each read after
    its source write).  Acyclicity by the A3(v) contraction, with the
    detail that makes it go: R's cross-hart edges are write-sourced
    (gmo|W, rfe), every hart segment exits through a WRITE, rule 14 maps
    each po-exit into gmo, and rfE is gmo-forward because cross-hart
    visibility has no po disjunct — the po-forwarding case of load-value
    is exactly rfi, which stays inside a segment.  So every R-cycle is a
    gmo cycle.  Linear-extension existence over the finite event set is
    hand-rolled topological selection (no stdpp helper).
  - THE CONSTRUCTION: place events in extension order; writes land in
    gmo order, so the cand log IS `gwrites`' message sequence and log
    positions equal `gwix` with NO renumbering; `cand_values` then falls
    out of load-value's value half plus rf-placement.
  - THE AXIOM TRANSFER (graph → `srvwmo_consistent` of the built cand):
    everything flows from gpos arithmetic — cand `ob_op` edges embed into
    G's gmo (ppo arms by `gppo_gmo`; fr by load-value CO-MAXIMALITY: a
    same-byte write not visible-before the read sits gmo-at-or-after it),
    so ob-acyclicity is a kless measure on gpos; `ax_ord`/`ax_rel_ord`
    derive the same way (e1 ord e2 gmo-forward; the fr target w is not
    visible-before e2, so gpos e2 ≤ gpos w and the published ts = wix e1
    < wix w on the write suborder); coherence via the A5 kit's
    `coh_rel_acyc_ts` with poloc-ts-monotonicity from rules 1–3.
    Estimate 600–1000 lines, one to two sessions, all order theory — no
    Iris, no simulation.

Plan of record: [`../design/weak-memory-layer2.md`](../design/weak-memory-layer2.md)
§8 (the route), §11 (the PARM investigation's answer), §13 (the walker
decision: the A/D RMW is non-promisable, as Sail fidelity).  The port spec is
[`../design/parm-certification-notes.md`](../design/parm-certification-notes.md)
— read it in full before any D8 item; its Recommendation section is the
per-item contract.  PARM reference sources: shallow clone at
`/tmp/claude-0/-shared-xv6iris-2/36d033b8-a541-4970-8c24-4e924a5dca1a/scratchpad/parm/src`
(re-clone `snu-sf/promising-arm` if evicted).

Goal: replace `robust_main_l2`'s site-fact hypotheses (`sf_edges`'s C4/C6
residue, `win_excl`) with theorems, by making every read of the full machine a
read of some pf run (the promise author's certifying run), so φ and the
WP-exported invariants apply to it.  No kernel side conditions anywhere.

## Items

- **W1 — walker-naming spike**: **DONE (2026-08-18) — GO** on the
  written-value discriminator, with conjunct (ii) REPLACED (see Findings).
- **W2 — realizing §13, PREMISE-FREE** (re-scoped 2026-08-18: the user
  REJECTS undischarged premises — the `no_early_ad` route is dead; see
  layer2 §13's addendum).  Blocked on the W1′ investigation below.  What
  survives regardless: the discriminator's bit-level facts (the spike's
  `update_PTE_Bits_A1`/`update_PTE_Bits_ne`, to land in `PtAdBits.v` when a
  consumer exists) and the one-line staleness fix to `WeakInterp.v`'s
  access-kind table (A/D path is `Read_RISCV_reserved`/
  `Write_RISCV_conditional` post-fork, not `Write_plain`).
- **W1′ — the premise-free walker analysis: DONE (2026-08-18).**  Verdict
  in layer2 §13's addendum: non-promisability necessary but NOT sufficient
  (variant B is a real, certifiable machine run — machine-checked probes
  `fulfil_ok_survives_walk_read`/`fulfil_vext_walk_read` in the
  walker-analysis scratchpad); the certification route closes NO walker
  shape; the recommended repair is W-TV (below).  Probe file worth
  harvesting when W2 lands.
- **W2a — the §13 gate, front-loading-safe form**: walker-shaped
  `LExStore` (named AT FULFIL from the reservation + the log's values —
  the spike's `ad_variant` discriminator, split-adapted) fulfils with
  release-strength `vpre` (join `w_vrOld ⊔ w_vwOld`).  Yields the TOP
  fact (its timestamp exceeds everything the agent read/fulfilled before)
  ⇒ closes every walker-write-EXIT segment; every store stays promisable;
  `wp_behavior_factor` untouched.  Land the TOP fact as a named Layer-1
  lemma.  Sequencing: with/after the split's S2 (it is a premise on the
  new `LExStore` arm).
- **W2b — W-TV, the missing translation ordering** (closes the
  walker-read-ENTRY shapes, variant B): bank the instruction's prior read
  timestamps `w_ldv`-style and join them into every memory-access node's
  `vaddr` (hence `w_vcap` via the existing `ctrl_post`), dying at
  `LInstr`.  No discriminator.  **ADOPTED (the user, 2026-08-18)** — the
  boundary sentence is recorded in layer2 §13; implementation per the W3
  entry's five conditions (note condition 1 refines the reset point:
  instruction BOUNDARY before the fetch, not `LInstr`), bundled into the
  split's S1 (`wstate`/`lstate` opened once).
- **W3 — the W-TV containment audit: DONE (2026-08-18), verdict (B) —
  ADOPT as a documented model-of-record boundary, awaiting the user's go.**
  Nothing in {(i),(ii),(iii)} contradicts the ISA: (i) is ASSERTED by the
  privileged spec ("those implicit accesses are ordered before their
  associated explicit accesses", `supervisor.adoc:1303-1304`); (ii) is not
  RISC-V-normative (RVWMO leaves walks unformalized) but is the ratified
  Arm VMSA `dob` clause (`[Imp & TTD & R]; tr-ib; [Exp & M]; po;
  [Exp & W | HU]`, Arm ARM B2.3.7) and RVWMO ppo rule 13's own rationale
  ("a store generally cannot be performed until it is known that preceding
  instructions will not cause an exception due to failed address
  resolution"); (iii) is deviation D-2, already landed.  Loads are
  deliberately NOT ordered (matches both Arm models).  The narrow variant
  is REFUTED concretely (`narrow_gap` probe: a two-instruction variant B
  survives it).  28 machine-checked probes in the wtv-audit scratchpad;
  the proposed boundary sentence is in the audit report, to be copied into
  layer2 §13 on adoption.
  **W2b's five conditions (from the audit — carry, don't rediscover):**
  (1) reset the translation bank at the instruction BOUNDARY, before the
  fetch (`pnode_step`'s `Ret` arm emits the reset, not `LSilent`) — with
  only the `LInstr` reset, the fetch's load consumes the previous
  instruction's data-read views and LB DIES; (2) a dedicated `w_tbank`
  joined with `fwd_view` only — NOT `w_ldv`, whose `vpre` component drags
  `w_vrNew` into every fulfil's EXT (probe `wtv_ldv_leaks_vrNew`);
  (3) add `LInstr` steps to `WeakPromiseLitmus.lbstep` and `WeakLitmus`'s
  toy language or their reachability theorems go false; (4) read the bank
  at each node's PRE-state (keeps the AMO's read half out of `w_vcap`);
  (5) the Layer-2 consumer already exists — `WeakRobustL2.fcov_of_vcap`
  turns a `vcapat` into `fcov`; only the `vcapat` producer at the access
  node is owed.  Also record with the boundary: the fetch's own
  translation reads gain the same edge, and misaligned/page-crossing
  component accesses become ordered (both RVWMO-unformalized; both
  vacuous for this image).
- **Fallback if W3 fails**: §12 option (b), the walker-idempotent exhibit —
  priced by W1′ as LARGER than the RMW split (walker READ discriminator =
  `pcls` state classification or a model fork; non-event-preserving replay
  re-bases `U_Qinv`/`head_prestate_pf_real`'s `pc_log = pf_log` framing; a
  new `walk_absorbing` Layer-1 parameter).
- **S-track — the RMW split** (design:
  [`../design/weak-memory-rmw-split.md`](../design/weak-memory-rmw-split.md),
  user-confirmed; gates D8-2's final shape and the L2 vocabulary):
  - **S0 — validation pass: DONE (2026-08-18)**, design revised from it.
    Size: ≈3,150 lines / ~40 files / ≈2,070 semantic.  Riskiest three:
    `WeakRobustSim.excl_ok_pf` (~230 ln, the pf-replay window straddles two
    events), the §5 retry arm's WP rule, `WeakRobustProv`'s `l_res` mirror
    (~150 ln).  Free: `WeakKpt*`/`WeakWalk*`/`WeakDeps`/litmus (zero
    change); net deletions: `fused_blk` + the `menvcfg.ADUE = 0` escape
    hatch + the `own_coh` dovetail.
  - **S0.5 — exhaustivise the 22 catch-all `wlabel` matches** (~150 ln,
    no semantic change; the 6 critical absorbers: `WeakEvInst.elab_log`/
    `edlab_log`/`pcls_ev`, `WeakSailLTS2.lbl_class`,
    `WeakRobustBlocks.lb_writes`/`lb_loads`; full site list in the S0
    report — sites at `WeakRobustGraph.v:111,121`, `WeakRobustL2.v:82`,
    `WeakRobustMain.v:140`, `WeakRobustAcyc.v:114,124,408`,
    `WeakRobustDisc.v:122`, `WeakRobustBlocks.v:90,94,100`,
    `WeakRobustOrd.v:217`, `WeakSailLTS2.v:316,370`, `WeakSailCone.v:419`,
    `WeakEvInst.v:158,500,559`, `WeakPromise.v:182`,
    `WeakPromiseFact.v:58`).  **Status: IN FLIGHT (2026-08-18).**
  - **R1 DONE** (`9f9ef678`, additive) and **R2 DONE** (`58e66071`,
    machine arms + reservation activation).  R2's findings of record:
    the store's reservation clear is PER BYTE in `store_post_d`/
    `store_post` (observationally identical to the run-level rule, saves
    ~20 rewrite sites); front-loading needed ZERO changes; the litmus
    repairs W3 condition 3 predicted are UNNECESSARY (the toy languages
    have no `w_vcap` consumer, and LB survives any consumption because
    the bank is read at the PRE-state — condition 4 is what does the
    work); `WeakCertify.astep_ok_del_vcap`'s conditional-write arm is
    the predicted one-liner.
  - **W-TV: HALF-LANDED.**  Production (`load_post_at` joins
    `fwd_view`-based bank) + reset (`instr_post`) are in;
    **CONSUMPTION (`ctrl_post … (vaddr ⊔ w_tbank)`) is DEFERRED to its
    own slice** — the `_d`-at-0 correspondence forces the bank into the
    non-`_d` tier (drags `WeakAxiomatic.mstep`, ~18 rewrite sites,
    `cfg_match`'s `w_vcap` equality, and the `lstate` mirror needing
    `l_tbank`).  Pickup spec: the 30-line comment at
    `WeakMem.load_post_run_d`.  Tier-1 does not need it (rule 14 gives
    the pf tier the ordering); sequence with tier-2 resumption or after
    A2.
  - **S4/R4 (pair-form tower re-index) — DONE (2026-08-20, T2-2a).**
    `WeakRobustSim.Qinv_step` and `WeakRobustCone.Qcfg_step` (the
    step-EXPORTING twin — it carries its own copy of all eleven arms, so
    every replay change lands twice) now replay `LExLoad`/`LExStore`
    directly, and `lat_free_prog`'s fused conjunct, `lat_free_prog_fused`
    and the old capstone's `Hfused` are DELETED.  What the pair costs, as
    three new obligations:
    * `ts_oblivious` gains an `LExLoad` conjunct (the instance proves it
      at ARBITRARY `asrc` — the exclusive read's operand list is real,
      D3-2 — via `WeakEvInst.pstep_ev_ts_exload`; the Sail LTS refutes it
      from `sail_step_fused`).
    * `pcls_obl` gains an `LExStore` conjunct: the conditional write
      APPENDS, so `wp_pf_step`'s class pinning reaches it.  Both provers
      (`pcls_ev_obl`, `WeakSailLTS2.lbl_class_obl`) reuse their `LStore`
      bullet verbatim.
    * THE RESERVATION crosses the replay in `WeakRobustProv`:
      `res_cols`/`aevs_post_res` (the replayed `w_res` is the recorded one
      with `rv_base` kept and `rv_ts` σ-mapped — `rv_view` is NOT related
      and no consumer needs it) and `aevs_post_res_src` (a recorded
      reservation names the `LExLoad` event of the same prefix that set
      it).  The window then transports by `WeakRobustSim.excl_ok_ts_pf`,
      `excl_ok_pf`'s trichotomy with the lower bounds' `gev_reads` facts
      taken at that EARLIER event (in `done` by `qorder_dc`).
    Supporting `WeakMem` equations: `load_post_run_d_res` /
    `store_post_run_d_res` / `fence_post_res` / `ws_init_res` — the
    per-byte clears mean an access clears `w_res` iff it has a byte, and
    the replayed and recorded folds take the same branch because they
    differ only in timestamps, never in a length.
  - **`WeakRobustBlocks.lb_ok` IS NOW THE ONLY ALPHABET GATE.**  Its
    `LExLoad`/`LExStore` clauses are still `False`; before S4 an instance
    that emitted the pair was excluded by `lat_free_prog`, now it is
    excluded here.  Harmless today (`lb_ok` has no prover outside that
    file, and nothing proves `lts_enabled` for the event instance), but
    the clauses need real content (`data ≠ []` + `WeakPromise.exwin_ok`)
    before any consumer of `lts_enabled` appears.
  - **Remaining: R3** (producers + retry arm + flips), **R6**
    (contract), the W-TV consumption slice.
- **D8-1 — `wp_cert_step` / `wp_certify` + the vcap lemmas**: **DONE
  (2026-08-18, `da090933`)** — `iris/WeakCertify.v`: `wp_cert_step i :=
  wp_astep_of i ∪ (∃ l, wp_pf_step i l)` (fully by reference, no arm
  duplicated), `prom_free`/`wp_certify`, `cert_step_vcap`,
  `cert_step_vcap_promise`, `rtc_cert_step_vcap_promise`, the contrapositive
  `rtc_cert_step_prom_free_vcap`, and `cert_step_rtc_wpstep` (a certifying
  run IS a full-machine run — `cfg_wf` replaces the bridge's `no_promises`
  premise via `prom_wf`'s length bound).  All closed under the global
  context.
- **D8-2 — the restriction simulation** (`sim_wpcfg`, PARM `CertifySim.v`'s
  arch-generic line): views equal below the boundary; every source message
  above the boundary is agent i's; the forward bank two-armed; `excl_ok`
  extended upward from the boundary.  The three deltas PARM does not have —
  budget against THESE, not view arithmetic: (i) the device fabric `pc_dev`
  (needs a `sim_dev`; reuse G4/G5's `qfab`/`gdev` machinery); (ii) `lat = true`
  reads (restrict certification to lat-free programs, as Layer 1 already
  does); (iii) the fused RMW (`sim_exbank`'s payload becomes an in-case
  obligation; reproduce `sim_mem1_exclusive` for `excl_ok`, per-byte over
  `tvs`).
- **D8-3 — completeness**: `promise_step_certify`, `interference_certify`
  (restriction direction), `eu_wf_interference`'s analogue, and
  `certified_exec_complete`'s backward induction from the terminal state.
- **E1 — the extended exhibit**: replay `U ++ certifying runs ++ the early
  read` as a pf run (the `U_Qinv` replay plus solo certifying runs);
  `head_prestate_pf_real` (L2-M2 §8.3) is the place it stands.
- **L2′ — the case analysis on extended pf runs**: φ refutes early reads of
  owned-unpublished messages (kills C5/C6's bad residue); sync bytes by
  machine facts + the exported lock-word value protocol (`wlockN` exports the
  values: RMWs write 1, releases write 0, an RMW reads its co-predecessor) —
  turns `win_excl` (SF-1) into a theorem.  Target: `robust_main_l2`'s
  hypotheses discharged with no site facts.

## Findings

(record per-item findings here as they land; rules and durable gotchas go up
to the design file / durable-notes, not narrative)
