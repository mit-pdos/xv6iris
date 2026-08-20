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
- **A1c — mechanization: DONE (2026-08-19, `01e17da1`).**  One
  presentation refinement worth knowing: rule 7 is stated TWICE — as
  `ppo_op`'s fifth arm (`rel_acq_po`, the global/ppo form) AND as
  `ax_rel_ord` (its gmo-consistency rendering in the file's local-axiom
  style: `rel_ord ; fr ; gmo|W` forbidden), because the counterexample's
  return leg is TIMESTAMP order on different-byte writes, which is not a
  `co`/`ob_op` edge — the local form is where the constraint bites.
  `rel_ord` = rule 7 composed through a non-empty acquire read with
  rule 5 (the acquire absorbs `w_vRel` into `w_vrNew`, so the release
  keeps ordering later steps); the empty-acquire exclusion is
  load-bearing.  `cand_rl_free` is GONE (A3(i) done);
  `srvwmo_consistent`/`srvwmo_realizable` are the named top level;
  `promise_free_complete_local` now uses FIVE local axioms,
  ob-acyclicity still unused.  Remaining premise: `cand_pub_clean`.
- **A3(ii) — DONE (2026-08-19, `27fb3c05`): T1 IS PREMISE-FREE.**
  `srvwmo_realizable c : srvwmo_consistent c → exec_wf (cand_exec c) ∧
  ex_tr … = cd_tr c ∧ ex_img … = cd_img c`.  The premise was replaced by
  the forward bank's replay-provable content (`cand_bankdom` +
  `cand_read_split`); `invw` unchanged; rule 12's omission is consumed
  INSIDE the theorem.  Non-vacuity both ways: `ce_fwd` is reachable AND
  refutes the old premise.  TIDY OWED (low priority): the dead `ctake`
  dictionary (~110 ln, old §2) and the stale prose at
  `WeakCompose.v:895` (says the completeness theorem still carries the
  two deleted premises — fix to "now premise-free" once the bridge files
  are quiet).
- **A3(iii) — DONE (2026-08-19, `9b1ce0f2`): `iris/WeakAxRealize.v`.**
  `exec_prog_ok`/`exec_wf_pf_run_prog` — the replay carries the real
  program per step; `prog_free` survives only as the trivial-assignment
  corollary (the bridge's own copies are now redundant, delete when that
  file is quiet).  THE INTERFACE: `lbl_realizes p σ i lb l` = `lb_fused
  l ∧ lat_free l ∧ lb_depfree l ∧ proj_lbl (pcls p l (ms_ws σ i)) l =
  Some lb` — the three gates are NAMED CONJUNCTS: A2's erasure deletes
  `lb_depfree`, the split lift (A3(iv)) deletes `lb_fused` (a fused
  axiomatic rmw ↦ the machine pair, `w_res` has no `mstate` image —
  same gate as the forward direction), `lat_free` is discharged by the
  instance (`pstep_ev_lat_free_prog`).  `exec_cls_ok` is GONE (absorbed
  into the projection equation).
- **A2 — DONE (2026-08-20): T2 IS CLOSED — `WeakEvInst.t2_ev`.**  Every
  promise-free run of the event instance projects to an `exec_wf`
  execution with the same image and THE SAME LOG, on exactly the 5 rv64d
  axioms, with NO premise beyond the two instance-discharged class facts
  (`pcls_ev_erasable`/`pcls_ev_fusable`): erasure ∘ re-fusion ∘ projection
  compose unconditionally.  A3(iv) (the fused↔split lift) had landed with
  stage 2; both directions name the same gates.
  **A2-s3 went through TWO same-day redesigns** — first: the landed
  `pstep_paired` was
  unimplementable for the instance (clause 1 unused; clause 2 cannot pin
  timestamps — same post-state from different-timestamp exloads; clauses
  2+3 jointly history-dependent at fence/load-reachable states, and the
  fetch is a plain `LLoad`, `AK_explicit`); second: the surviving
  four-clause program discipline was itself UNNECESSARY — see s3c/s3d
  below.  The full record is the design doc's stage-2 block; the slices:
  - **s3a — DONE (2026-08-20)**: `WeakMem.load_post_at` clears `w_res`
    per byte; `fence_post` clears CONDITIONALLY on any bit set — the
    ALL-FALSE fence is exempt because it is `fence.i`'s inert rendering
    (`LSilent` in the wp-machine LTS, the (D2) label in the ev tier, and
    `fence_post_id` — now in `WeakMem` — is load-bearing in
    `WeakEvInst.elab_apply_barrier`).  Blast radius measured by full `-k`
    builds: two `ws_bounded` proofs in `WeakMem`, two `res_rel` bullets in
    `WeakErase` (both sides clear → vacuous; the fence one splits 16 ways
    on the bits), and NOTHING else — every concrete wp-tier state has
    `w_res = None` outside windows and windows contain no loads/fences,
    so the 17k mirror and all litmus/leaf proofs were value-unchanged.
  - **s3b — DONE, then SUPERSEDED same day**: the first reshape kept a
    four-clause PI-guarded program discipline (`expend`/`PI`; W1 inert
    pull-back, W4 zero-byte-load vacuity, W3 exstore-pending) whose
    instance discharge priced out at a whole-model `riscv_step` shape
    traversal (s3d, the `gpost`/`goodbP` driver family).  Re-deriving the
    per-arm needs then showed the machine guard suffices alone:
  - **s3c/s3d — RETIRED (the second redesign)**: dropping the `expend`
    guard from the pending invariant (`∀ R, w_res = Some R → rf_pend`)
    makes it SELF-MAINTAINING — established unconditionally at the
    exload, carried verbatim across inert steps (the zero-byte load's
    dep-free `vaddr = 0` makes both post-states literal identities,
    `load_post_run_d_nil`; the all-false fence is `fence_post_id`),
    killed by the guard at dirty labels, consumed at the exstore whose
    machine premise IS the guard.  `pstep_paired`/`expend`/`PI` are
    DELETED from `WeakRefuse`; every case that refuted a program
    predicate (bare `lr`/`sc` decode branches, clean-vs-dirty history
    aliasing at one state, the PLIC's mid-window `sig_seip` write,
    timestamp pinning) is a non-case for the machine guard.
  - **s3e — DONE**: `WeakEvInst.t2_ev`, the instance endpoint.
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
- **A5 — DONE (2026-08-20): `iris/WeakSrvwmoLitmus.v`** — the litmus
  suite against `srvwmo_consistent` ITSELF (design S5; corollary (b)'s
  evidence artifact).  Nine verdicts, all 17 theorems
  `Print Assumptions`-closed.  POSITIVES (SB 0/0; MP-no-fence;
  MP-writer-fence-only; AMO reads-latest) are concrete consistent
  candidates discharged AXIOM-BY-AXIOM via `cand_plain_ok` — the kit
  that reduces `cand_axiomatic_ok` to `ax_atomicity` for a candidate
  with no sr-covering fence / no acq-po edge / no release / no same-byte
  po — NOT via machine reachability, so each is a verdict about the
  definition, with the machine run a corollary through `srvwmo_run`
  (T1).  NEGATIVES (LB; MP-both-fences and MP-acquire via `ax_ord`;
  MP-reader-fence-only via `ax_ord` + rule 14; CoRR via `ax_coherence`)
  quantify over EVERY conformant candidate on `img0`, machine
  corollaries via `srvwmo_of_wf`.  The file's §9 table records the TWO
  deliberate RVWMO divergences, both rule 14's: (1) LB — forbidden by
  the LOAD-VALUE axiom alone (`lb_values_forbidden` consults no
  ordering axiom; no-thin-air is definitional in the candidate
  presentation), and (2) MP-reader-fence-only — rule 14 makes the
  writer's fence redundant where RVWMO allows the stale read.  So
  corollary (b)'s slogan ("LB unobservable, everything else matches
  riscv.cat") needs the recorded caveat: rule 14 narrows the class by
  MORE than LB.  §3's acyclicity generalizations (RMW admitted, the
  rule-14 `ppo_op` arm admitted; `ets_lt_wr` factored) cost ~70 lines,
  as priced against WeakAxiomatic3 §15(1)'s ~150.  §8 keeps the
  not-done ledger with prices: IRIW (~150 ln, needs write-order
  totality — free in trace order — plus two opposed `ax_ord`
  instances), SB-fenced both directions (its `rw,rw` fences have
  `sr = true`, so `cand_plain_ok` does not apply), the atomicity
  negative (~50 ln), and the split-exclusive shapes (R-track's, not
  this alphabet's — the model keeps exclusives fused).
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
