# The certification route (D8 / E1 / L2′) — worklist

## CHECKPOINT (2026-08-20, end of the tier-1-closure + tier-2-opening
## session) — READ THIS FIRST WHEN RESUMING

**Where things stand.**  TIER 1 IS CLOSED (`xv6_srvwmo_safe` + `t2_ev` +
the litmus suite, all on the five rv64d axioms — see the sRVWMO worklist).
S6 ran with verdict GO (route A, certification;
[`../design/weak-memory-tier2-s6.md`](../design/weak-memory-tier2-s6.md)).
Tier-2 slices LANDED this session, in commit order: **T2-0** (the
lock-protocol export, `WLock`/`wlat4L`/`weak_ev_adequacy_lockproto`),
**T2-1a** (`iris/WeakRvwmoGraph.v` — RVWMO⁻ declared + the LB
non-collapse witness), **T2-2a = S4** (the tower replays the split pair;
`lat_free_prog` is lat-only; the capstone's `Hfused` is DELETED — the
tier-2 containment capstone is instantiable for the real instance again).
Every landed piece keeps both capstones at EXACTLY the five reservation
axioms; re-verify that audit after any change.

**THE PENDING DESIGN DECISIONS — each needs an orchestrator design pass
BEFORE building; none is delegate-ready as it stands:**

- **(D-i) W-TV CONSUMPTION, the tier decision** (gates L2′'s walker
  cases #7/#8, NOT D8-2).  The in-tree spec is the long comment at
  `WeakMem.load_post_run_d` (~:1035): joining `w_tbank` into the access
  node's `w_vcap` moves three things in lockstep — the `_0`
  correspondence (dragging the bank into the NON-`_d` tier:
  `WeakAxiomatic.mstep`, the litmus tier, ~20 call sites),
  `WeakPromiseBridge.cfg_match`'s per-agent `w_vcap` EQUALITY, and
  `WeakRobustProv`'s `lstate` mirror (needs `l_tbank`).  THE STAKES the
  comment predates: `mstep` now carries T1
  (`promise_free_complete_clean`) and the whole tier-1 characterization —
  changing its load arm touches the completeness invariant.  Candidate
  resolutions to weigh: (α) push the bank into the non-`_d` tier and
  repair T1's invariant (honest, widest ripple); (β) keep the bank
  `_d`-only and WEAKEN the `_0` equations to ≤-form where consumed;
  (γ) make `cfg_match` stop looking at `w_vcap` (check what the bridge
  actually needs it for first).  Decide against T1's proof structure,
  not against the comment alone.
- **(D-ii) W1/W2 — the walker discriminator wiring.**  Verdicts already
  recorded (layer2 §12/§13 + this file's W-track): the written-value
  discriminator (GO), W2a's release-strength-EXT-at-fulfil form, the two
  recorded obstacles to a promise-side gate.  What remains is the
  realization: name walker-shaped `LExStore` at fulfil from the
  reservation + log values, gate non-promisability there, re-prove
  `wp_behavior_factor` compatibility.  Design pass: pick the
  discriminator's exact site against the R2 machine arms.
- **(D-iii) T2-3 = D8-2, the restriction simulation** — the route's
  highest-risk item.  Before building: design `sim_wpcfg`'s four
  invariants against PARM's `CertifySim.v` (port spec:
  [`../design/parm-certification-notes.md`](../design/parm-certification-notes.md),
  Recommendation section — start with the two `vcap` lemmas), design
  `sim_dev` (the fabric component PARM lacks; reuse bet: G4/G5's
  `qfab`/`gdev` machinery), and the split-RMW in-case obligation
  (`excl_ok` per byte in the restriction).  THE FALLBACK TRIGGER IS
  ARMED: if `sim_dev` exceeds the `qfab`/`gdev` reuse estimate, STOP and
  switch to route B (S6 §5's graph linearization route).
- **(D-iv) T2-5's export seam** — recorded under T2-0 below: `wlock_regd`
  is per lock word; upgrade to a finite set of `(base, N)` pairs if L2′
  wants a family at once; and the trace-side `win_excl` derivation must
  take unlock COVERAGE from trace fences, never from message class (the
  release arm is `≠ WCplain ∧ zero`).
- **(D-v) T2-6's front-end remainder** — `gx_deps` (the store-dep
  fragment, S6's F2 caveat) added to `WeakRvwmoGraph` when the
  realizability direction starts, and the `axiomatic_to_promising` port
  (promise everything up front; M6's W4 characterization is the banked
  half).
- **(D-vi) the `lb_ok` debt** (surfaced by S4): `WeakRobustBlocks.lb_ok`
  is now the ONLY alphabet gate and its `LExLoad`/`LExStore` clauses are
  still `False`; they need real content (`data ≠ []` + `exwin_ok`)
  before any `lts_enabled` consumer appears.

**Recommended resumption order**: (D-i) design → build (it is the
smallest gate and unblocks L2′'s walker kills); then (D-ii); then the
T2-1c build (design fully recorded below — pure order theory, no Iris);
then (D-iii) with the fallback watch; E1; L2′; T2-6.  R6 (the fused-
machinery deletion contract) stays last — cleanup, not gating.

**Fixed working discipline that held all session**: orchestrator (Fable)
does recon + design + spec; Opus subagents execute mechanical
proof/threading from precise specs with the durable-notes build
discipline quoted; every landing is verified independently (full `-k`
build + both capstone audits) before commit; findings that change
statements are recorded in the notes the same day.



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
  - **W-TV CONSUMPTION: LANDED (2026-08-20, the D-i slice, option α).**
    All four run functions wrap in `ctrl_post … (vaddr ⊔ w_tbank
    ws-at-ENTRY)`; the `_0` equations became CONVERSIONS (`Nat.max 0 x`
    reduces) and `cfg_match` needed zero edits.  The vcapat producer's
    WeakMem half is `load_post_run_d_tbank_vcap` + store twin.  What it
    cost, all premise-free: (i) `WeakLitmusProj.lcfg_match` weakened
    from state EQUALITY to `ws_ctrl_up` ("equal but for a raised
    control view") — THE GENERAL RULE: after α, any relation equating
    a per-byte-stepping machine's `wstate` with a run-level one is off
    by a `ctrl_post`, and `WeakMem.ws_ctrl_up` (+ `ctrl_post_ctrl`,
    `load_post_at_ctrl`, `load_post_run_d_ctrl`) is the vocabulary;
    (ii) the erasure's `er_ws` runs on `ws_le_nc` (the vcap conjunct
    DELETED, per the design finding); (iii) `lstate` gained the
    `l_tbank` mirror (11th `lrel` conjunct, appended so positional
    patterns survive; the tower replay in Sim/Cone transported it FOR
    FREE through `lrel_aev_post`).  A ZERO-WIDTH ACCESS IS NO LONGER
    INERT (`ts = []` still consumes the bank): "empty access moves
    nothing" reasoning now needs a `w_vcap`-blindness lemma
    (`invw_ctrl_post`, `rf_ws_ctrl`).  L2′'s remaining owed piece from
    W2b condition 5: the trace-level `vcapat` producer at the access
    node, to be designed with the L2′ slice.
  - **Remaining: R3** (producers + retry arm + flips), **R6**
    (contract).
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

- **D-i DECIDED: option α (2026-08-20, orchestrator design pass; build in
  flight).**  The bank enters the non-`_d` tier symmetrically — both
  `_run`/`_run_d` families take `ctrl_post … (vaddr ⊔ w_tbank ws-at-ENTRY)`
  — so the `_0` equations and `cfg_match`'s equality stay EXACT.  The recon
  that decided it: T1's `invw` (`WeakAxiomatic3.v:1298`) never mentions
  `w_vcap`/`w_tbank` (the whole file has zero references), and `ctrl_post`
  is a `w_vcap`-only update, so α is invariant-transparent for T1; β would
  smear ≤-side-conditions over ~20 call sites to avoid churn that is
  mostly mechanical; γ's motivation dies once equality is free.  THE ONE
  REAL CASUALTY is the ERASURE: `er_ws`'s `ws_le` carries a `w_vcap`
  conjunct, and post-α the erased side's vcap can OVERTAKE the instance's
  (instance resets `w_tbank` at `LInstr`; the erased run maps `LInstr` to
  `LSilent` and never resets).  Resolution: DELETE the vcap conjunct from
  the erasure relation (a `ws_le_nc` bundle) — justified by `WeakErase`'s
  own header (the pf fragment has no `fulfil_ok`, so `w_vcap` never
  appears in a side condition), and verified consumer-free
  (`ws_le_vcap`'s uses are all machine-step monotonicity chains;
  `WeakRefuse` never mentions vcap).  A deletion, not a premise.  Also
  verified in design: the toy-tier LB proof SURVIVES full consumption
  with no `LInstr` in the toy language, because `fulfil_ok` reads the
  PRE-state's `w_vcap` and the fulfilling agent's own bank is produced
  but not yet consumed at fulfil time (this is what W2b condition 4
  buys); and the fused `LRmw` composition `store_post_run ∘
  load_post_run` consumes the intermediate bank on BOTH tiers equally,
  so the split/fused correspondence is undisturbed.  Slice spec:
  scratchpad `di-spec.md`.
- **T2-1c SHARPENED in the spec pass (2026-08-20): no topological
  selection needed.**  Two upgrades over the recorded design: (i) ALL rf
  edges are gmo-forward — the forwarding (rfi) case is same-byte po, so
  ppo rules 1–3 (`gpoloc ⊆ gppo ⊆ gmo`) already order it — so the
  extension order needs no rfi special-casing; (ii) the linear extension
  has a CLOSED FORM: for each write in gmo order emit its hart's
  po-segment ending at that write, then the write-less tails —
  equivalently sort by the injective key `(gpos of next-po-write, hart,
  position)`.  Rule 14 fires in exactly two places (same-hart segments
  appear in po order; a read precedes its own next write, which places
  it after its rf source's segment).  Acyclicity never needs stating —
  each cand obligation is proven directly against the enumeration.
  Slice spec: scratchpad `t21c-spec.md` (build in flight, worktree).
- **D-ii REALIZATION SITE PICKED (2026-08-20, design pass; build queued
  behind D-i).**  The discriminator lives in `WPExStore`'s `fulfil_ok_d`
  view argument: when the written `data` is the A/D update of the values
  the reservation's read observed (`data = bytes of pte_set_ad read 1 d`
  ∧ `data ≠ read`, the spike's classifier — read values recovered from
  `pc_log`/`pc_img` at `rv_ts`, all fulfil-time data), join
  `w_vrOld ⊔ w_vwOld` into the EXT floor.  Nothing else changes: the pf
  fragment has no `fulfil_ok` (tower replay untouched), constructors
  that append at the fresh top satisfy any floor (front-loading and
  D8-3's certify-then-fulfil pay nothing), and inverters get W2a's TOP
  fact directly.  The spike's `update_PTE_Bits_A1`/`update_PTE_Bits_ne`
  land in `PtAdBits.v` with this slice (probe file:
  session-`0f027e1d` scratchpad `walker-spike/WalkDisc.v`, still
  present and building against in-tree `PtAdBits`).
