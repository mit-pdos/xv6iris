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
- **W1′ — the premise-free walker analysis** (investigation): does
  walker-write non-promisability even SUFFICE for `gdep2_acyclic` (the §8
  cycle's variant with the ORDINARY store `f` promised early and the walk
  READ late may survive it); if not — or since a machine gate is blocked
  anyway (no label at `WPPromise`; append-at-fulfil breaks front-loading) —
  which theorem route closes walker-entry segments: the certification
  analysis (L2′ treating the walker edges like any early read) or the
  walker-idempotent exhibit (§12 option (b)), and what each costs.
  **Status: IN FLIGHT (2026-08-18).**
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
