# sRVWMO — tier-1 worklist (the characterization + capstone restatement)

Plan of record: [`../design/weak-memory-srvwmo.md`](../design/weak-memory-srvwmo.md)
(its §6 names the items S1–S6; this file carries their execution state).
To avoid collision, the RMW-split slices (certification worklist S-track)
are renamed **R0.5–R6** as of 2026-08-19; sRVWMO items are **A1–A5** here
(A_n = the design doc's S_n), plus **A0** (inventory).

## Status (2026-08-19, orchestrator; staging PROPOSED, awaiting the user's
## reaction to the plan message)

- **A0 — asset inventory**: what `WeakAxiomatic.v` / the bridge /
  `WeakCompose` §6(5) / the litmus tier already give A1/A2/A3.
  **IN FLIGHT.**  Known already: `WeakAxiomatic.v` has the vocabulary,
  executions, po/rf/gmo/co/fr, the RVWMO-minus-deps axiom set, and the
  SOUNDNESS direction PROVED (`promise_free_sound`) — i.e. T2 at that
  vocabulary is essentially done modulo the dep upgrade and the
  projection; T1 exists only as the slice-2 conjecture at the file's
  bottom.  The file's "machine tracks no register views" scope note is
  STALE (D2/D3 landed).
- **A1 — the sRVWMO definition** (design doc S1): extend `WeakAxiomatic`
  with (a) rule 14 incl. its R×W half in the writes-only-gmo vocabulary,
  (b) the dependency vocabulary (ppo 9–13 need dep information in the
  axiomatic alphabet — the 4-label `lbl` carries none; without them T1 is
  FALSE, since the machine enforces deps), (c) the fabric/disk story,
  (d) the honest `.rl`/ppo-6 residue, (e) dangling exclusive reads
  (project as plain reads; paired AMOs stay fused axiomatically).
  Orchestrator writes the spec after A0; subagent mechanizes.
- **A2 — T2 completion**: keep/extend the soundness theorems under A1's
  added axioms + prove the PROJECTION (event-language pf runs ↔ the
  axiomatic machine) so T2 speaks about the real carrier.
- **A3 — T1 realizability (the tier-1 long pole)**: pf-AtoP.  Shape:
  linearize po ∪ co ∪ rfe (acyclic by rule 14); simulation invariant
  (log = gmo-order stores so far; per-hart views bounded by
  prefix-derived positions; forward bank; reservation); per-event
  enabledness lemmas (readable/fulfil_ok/excl_ok from the axioms);
  induct; instantiate at the event language.  Recipe: PARM `AtoP.v`
  minus promises — rule 14 is exactly what makes the promise-free
  construction schedulable.  Orchestrator writes the invariant design
  doc first.
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
