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

- **W1 — walker-naming spike** (investigation, no tree changes): evaluate the
  written-value discriminator for the walker's A/D RMW (§12's first
  mechanism): definition in the tree's vocabulary, false-positive analysis
  (software AMOs), where the non-promisability gate would live in
  `iris/WeakPromise.v`, cost estimate.  Fallback if NO-GO: the `pcls`-style
  state classification.  **Status: IN FLIGHT (2026-08-18).**
- **W2 — the machine change** (blocked on W1): walker A/D RMW append-at-fulfil
  (non-promisable) in the full machine, per §13; containment argument
  (restricted ⊆ unrestricted is trivial; the fidelity boundary is §13's
  bullet); re-land whatever the gate touches.
- **D8-1 — `wp_cert_step` / `wp_certify` + the vcap lemmas**: the
  certification step relation (agent i's `wpstep` arms minus `WPPromise`,
  unioned with `PFStore`/`PFRmw`), `wp_certify`, and the ports of PARM
  `Certify.v:128/144/166` (`cert_step_vcap`, `cert_step_vcap_promise`,
  `rtc_cert_step_vcap_promise`) — EXT ⊒ `w_vcap` is the proof content, D-2
  already supplies it.  New leaf file `iris/WeakCertify.v`.
  **Status: IN FLIGHT (2026-08-18).**
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
