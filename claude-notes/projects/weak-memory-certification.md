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
- **W2 — realizing §13** (blocked on: the fused-RMW change the user has
  announced, and the user's confirmation of the premise shape): the
  discriminator `wlb_ad` (stdpp-only, beside `WeakMem`) + the ~30-line
  `PtAdBits.v` bridge (`update_PTE_Bits w acc = Some w' → ad_variant w w'`;
  the two hard bit-facts are proved in the spike's scratch file) + §13 stated
  as the traced-bundle premise `no_early_ad` threaded through
  `robust_main_l2` — NOT as a `WPPromise`-side machine change (see Findings
  for why that is architecturally blocked).  Also owed here: the one-line
  staleness fix to `WeakInterp.v`'s access-kind table (A/D path is
  `Read_RISCV_reserved`/`Write_RISCV_conditional` post-fork, not
  `Write_plain`).
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
