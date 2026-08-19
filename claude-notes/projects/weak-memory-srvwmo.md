# sRVWMO — tier-1 worklist (the characterization + capstone restatement)

Plan of record: [`../design/weak-memory-srvwmo.md`](../design/weak-memory-srvwmo.md)
(its §6 names the items S1–S6; this file carries their execution state).
To avoid collision, the RMW-split slices (certification worklist S-track)
are renamed **R0.5–R6** as of 2026-08-19; sRVWMO items are **A1–A5** here
(A_n = the design doc's S_n), plus **A0** (inventory).

## Status (2026-08-19, orchestrator; staging PROPOSED, awaiting the user's
## reaction to the plan message)

- **A0 — asset inventory: DONE (2026-08-19).**  Headline corrections to
  this file's earlier priors: **T1 already EXISTS for a fragment** —
  slices 2/3 landed 2026-08-12 as `iris/WeakAxiomatic2.v` (`cand`,
  `cand_exec`, `gmo_op`/`opos`/`okey`, `ppo_op` — whose FIRST ARM IS RULE
  14 in full, `ppo_op_gmo`, `promise_free_ob_acyclic`, `cand_reachable`,
  `sc_cand_reachable`) and `iris/WeakAxiomatic3.v`
  (`promise_free_complete_clean` :1340 under `cand_shape ∧ cand_values ∧
  cand_rl_free ∧ cand_pub_clean ∧ cand_axiomatic_ok`;
  `promise_free_complete_local` :1360 — only FOUR local axioms used,
  ob-acyclicity NOT needed).  The unrestricted conjecture is
  machine-checked FALSE (`promise_free_complete_false` :1793,
  `view_domination_false` :1809): the release→acquire arm
  (`w_vRel → load_vpre` on `.aq`) is enforced by the machine and absent
  from `ppo_op`.  The event-level ob form is also refuted
  (`ev_rfe_co_fr_cyclic`, WeakAxiomatic2:1109) — operations, not events,
  are the granularity.  THE PROJECTION BLOCKER: `wp_pf_bridge`
  (WeakPromiseBridge:692) needs `pstep_depfree`, FALSE for xv6 post-D3 —
  dissolves only when the axiomatic alphabet carries deps.
  `WeakCompose` §6(5) is prose, not a theorem.  The safety (reducibility)
  form of event-language adequacy does not exist yet (two-line pattern
  from `WeakAdequacy.v:131/:285`).  Capstone check CONFIRMED:
  `main_premises` is a hypothesis (WeakEvCapstone:919-925), so R4 defers
  and the tree stays green — caveat: the per-`pstep_ev` facts
  (`pdev_ev_ok`, `pstep_ev_lat_free`, `_ts_load/_ts_rmw`, `_ldepfree`,
  `pcls_ev_obl`, `efulfil_acct`, WeakRetag) need per-arm additions in
  R2/R3.  Full ledger in the A0 report (session transcript).
- **A1 — the sRVWMO definition** (design doc S1; orchestrator spec, then
  a subagent mechanizes).  The settled shape, from the refutations:
  sRVWMO's ppo = RVWMO rules **1–5, 7, 9–11, 13, 14**, with **rule 6
  OMITTED** (machine is weaker: `.rl` feeds only `w_vRel`; omission is
  SAFE — it widens the model, and the final theorem quantifies over all
  sRVWMO executions), **rule 12 WEAKENED per D-7** (forwarded reads bank
  0), **rule 8 replaced** by an `rmw : ev → ev → Prop` relation + the
  RVWMO atomicity axiom `rmw ∩ (fre;coe) = ∅` (split-ready; a DANGLING
  exclusive read is a plain read).  The rel→acq arm = the machine's
  `w_vRel` version, noting it coincides with RVWMO rule 7 under RISC-V's
  all-RCsc annotations — NOT a strengthening beyond RVWMO.  Rule 14 =
  `ppo_op` arm 1, already landed.  Deps: the alphabet gains
  `asrc`/`vsrc` on `LStore`/`LRmw` (per D-8, not on loads) + reg-write/
  ctrl events or a per-event dep relation; `mstep` moves to the `_d`
  step functions.  Fabric: a SCOPE CLAUSE — sRVWMO covers RAM accesses
  of harts + the disk agent; MMIO/UART/PLIC are outside, under the
  retained MMIO-ordering assumption.  Presentation: consistency is
  defined over `cand` (trace presentations), the landed shape; the
  partial-order form is later sugar.
- **A2 — T2 completion**: extend the soundness theorems for the new
  arms; the projection unblocks once the alphabet carries deps
  (`proj_lbl` keeps operand lists; `cfg_match` equality then holds with
  `_d` step functions).
- **A3 — T1 completion** (much smaller than feared — the induction
  exists): (i) drop `cand_rl_free` by adding the rel→acq `ppo_op` arm
  and extending the view-domination lemma's dominator case; (ii) drop
  `cand_pub_clean` — proof-side only post-D-7: re-prove §8's
  `w_vrOld`/`w_vrNew` conjuncts for a forwarded read (+ the ~150-line
  §13-shortcut generalization WeakAxiomatic3 §14(1) prices); (iii) the
  program-carrying form of `exec_prefix_pf_run` (replace `prog_free` by
  a per-step `pstep` supply; re-index `exec_cls_ok`); (iv) the
  split-exclusive atomicity re-proof (replaces `cand_rmw_latest`'s
  own-write-at-top shortcut; after R3); (v) the graph→cand scheduling
  lemma if the partial-order presentation is wanted (linear extension of
  po ∪ gmo|W ∪ rfe; acyclic via rule 14's contraction argument — NOT
  gmo ∪ po, which SB refutes).
- **A4 — tier-1 capstone**: adequacy ∘ T1; `Print Assumptions` audit
  (platform axioms + no-icache + funext + WP package; NO
  `main_premises`).
- **A5 — litmus verdicts against the DEFINITION** (not just the machine).
- **S6 (tier-2 gate, unchanged)**: the two-hart L2′ paper exercise —
  before any further D8 porting (D8-1 predates the gate; it stands,
  parked).

## Interaction with the R-track (RMW split) and the parked tier-2 assets

- The split is ON the tier-1 critical path: T1 quantifies over programs,
  and sRVWMO executions include DANGLING exclusive reads (walker O-FRESH,
  AMOCAS mismatch); the fused event language is STUCK there, so T1 is
  unprovable against it.  R0.5–R3 (+ mechanical R5) precede A3's
  instantiation; **R4 (the robust-tower re-index) is DEFERRED to tier 2**
  provided the old capstone takes the graph package as hypotheses (A0
  confirms).  The retry arm resolves stuckness for adequacy; T1 never
  meets it (it schedules each exclusive pair contiguously).
- Parked for tier 2, not wasted: `WeakCertify.v` (D8-1), W2a (the
  release-EXT walker gate), W2b/W-TV (adopted; rides R1 so
  `wstate`/`lstate` open once — its consumers are tier-2 only), the
  L2-M1/M2 tower, `robust_main_l2`.
