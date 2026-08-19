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
- **A1a — the dep-vacuity probe: DONE (2026-08-19).**  The orchestrator's
  claim FAILED in mechanism, HOLDS in conclusion for the D-8 alphabet:
  the pf machine's fulfil side is fully vacuous at the top timestamp
  (BOTH `fulfil_ok_d` conjuncts — `fulfil_ok_d_top`), but `read_ok_d`'s
  `vaddr` floor IS a live load-side binding site (machine-checked MP+addr
  witness: with `asrc = [DReg 1]` the stale read is NOT a step) —
  unreachable at the instance only because D-8 pins loads to
  `asrc = []` (`pstep_ev_ldepfree`).  The rmw read half is vacuous via
  `pf_rmw_latest` + `latest_readable`; the forward bank via the NEW
  `dep_dom` invariant (every dep view ≤ `w_vrOld` at pf-reachable
  states, ~90 ln, must land).  Probe files preserved at
  scratchpad/a1a-depvacuity-keep/ (18 lemmas, closed).  Projection
  route chosen: the ERASURE SIMULATION (see the design doc's settled
  block); fallback `mstep_d` prototyped (~1 line/arm, blast radius = 9
  files of exhaustive `lbl` matches).
- **A1 — the sRVWMO definition (settled — the design doc §1's "SETTLED
  AXIOMATIZATION" block is normative)**: ppo = RVWMO rules **1–5, 7, 14**
  ONLY; 6/8/10/11/13/9-store redundant under 14; 9-LOAD omitted BECAUSE
  OF D-8 (returns if D-8 drops); 12 omitted via `dep_dom`.  Exclusives
  stay FUSED axiomatically (projection re-fuses; dangling read = plain
  load) — the earlier `rmw`-relation idea is RETIRED.  Mechanization
  (A1c): the rel→acq `ppo_op` arm + view-domination extension; land
  `dep_dom`; a named top-level `srvwmo_ok`; the residue notes as
  comments.  BLOCKED ON R1's commit (shared tree in flux).
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
