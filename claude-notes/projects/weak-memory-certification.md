# The certification route (D8 / E1 / L2′) — worklist

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
  `LInstr`.  No discriminator.  BLOCKED ON: W3's audit verdict, then the
  user's go (it is a model-of-record ordering addition).  If adopted,
  bundle into the split's S1 (`wstate`/`lstate` opened once).
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
  - **S1–S6** per the design file's §8 (expand/contract; S1 additive with
    `LRmw` still present; S6 the contract).
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
