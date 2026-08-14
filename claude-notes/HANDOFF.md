# SESSION HANDOFF — 2026-08-14 (weekly limit hit; branch `weak-memory`)

**State: everything is committed and pushed to `origin/weak-memory`
(HEAD = bf66a775).  The tree builds green; `git status` clean; no
background work in flight; nothing is lost.**  This file is the entry
point for the successor agent.  Read `README.md` → `durable-notes.md`
first as always; then the worklists below in this order.

## Where the weak-memory effort stands (one paragraph)

The architecture pivoted (user-approved) from the two-machine
instruction-atomic lift to the EVENT-GRANULAR LANGUAGE — the logic's
machine IS the promise-free machine.  The spike PASSED at measured time
parity (design: `design/weak-memory-event-granular.md`; spike record:
`projects/weak-memory-event-lang.md`).  The Layer-1 FABRIC
GENERALIZATION (shared device component; worklist:
`projects/weak-memory-fabric.md`) is landed through G6a; the effort's
remaining step is G6b.  The superseded machinery (the lift, the shape
towers, premise-elimination) is retained side by side as the failure
record — 15+ machine-checked findings; do NOT delete it.

## THE IMMEDIATE NEXT STEP (G6b — precisely recorded)

In `projects/weak-memory-fabric.md`'s G6 landing notes, step by step:
1. **Retype `pcls : P → wlabel → wstate → wm_class`** (currently one
   argument short: `wlabel` cannot see a conditional RAM write — the
   access kind lives in the residual monad node; xv6 hits this on every
   acquire; the archived ⇒ bracket carries `wrun_plainw` because of it,
   no capstone does).  The replay is unaffected (`qcfg` hands the
   recorded `pa_st` verbatim).
2. Exhibit the event language's `epf_step` as the instance of the
   generalized `wp_pf_step` (pcls := the language's class function;
   pdev per G5's spec; PLIC hart index via CPU in PHart — recorded
   cheap fix).
3. THE ONE-MACHINE CAPSTONE: event-language adequacy
   (`weak_ev_pf_violation_free`, zero glue premises) + generalized
   Layer 1 (`robust_main`, witness form) end to end.  Premises:
   `main_premises` (now incl. `dev_epoch_ok` and the §6(3′)
   `cls_canonical` normalization) + fresh era + `img_total` + WP
   package + the 5 rv64d axioms.  Keep the archived capstones
   compiling.
4. Wrap: `WeakCompose` §6 final ledger; fabric worklist closed;
   `Print Assumptions` = exactly the 5 axioms.

KNOWN CONSTRAINTS (all machine-checked; do not re-attempt): the
disk-flat `pstep` input is REFUTED (flat reads are `latest_ts`-indexed
= the lat=true shape `lat_free_prog` excludes; delta (i) is irreducible
at Layer 1 — M5 device views is the fix; the honest residue is a
reachability-INCLUSION premise, not memory-blindness).  Class pinning
lives on the PF FRAGMENT ONLY (pinning the full machine falsifies
`WeakRetag.wpstep_retag`, and the retag DISCHARGES `cls_canonical` —
it is load-bearing).

## After G6b (the regroup agenda agreed with the user)

1. **M4 leaf retarget** (volume track): port the weak-tier leaves to
   the event language with SPEC-PRESERVING packaging (the certification
   adapter keeps leaf statements byte-identical; whole-function proofs
   re-check untouched).  Benchmark: spike parity ≈1.03–1.19× time.
2. **Phase-2 discharge** of `main_premises` (exhibit-level consumption
   from per-site WWP tokens — `projects/weak-memory-premises.md`'s
   phase 2, which SURVIVES the pivot).
3. **RVWMO axiomatization** (research track): upgrade the PARM
   containment note to a machine-checked theorem; groundwork in
   `WeakAxiomatic2/3`; note the class-pinning addendum to the
   containment note.
4. **The main-branch Cycle port** is fully specified in
   `design/main-cycle-port.md` (a self-contained hand-off document the
   user requested for a main-branch agent; no weak-memory content).

## Coordination notes

- The 6c/walk-bridge session: a RETARGET NOTICE sits at the top of
  `design/weak-memory-walk-bridge.md` — the event pivot dissolves that
  effort's founding problem; new 6c work should target the event tier,
  not `WeakStale`.
- The M4 port (SC→weak sweep) should NOT resume against the
  instruction-atomic interface — retarget per item 1 above.

## The session's findings ledger (details in worklists + commit log)

Twelve-plus machine-checked findings, all of the same genre —
over-quantified ∀-statements about the model/machine refuted by real
behaviors: the oracle-stream unsatisfiability, O1–O11 (shape/liveness/
decoder/ExtraOutcome/window series), W7 (rf points backwards in
behavior time — promise reads), the wp_pf_step over-approximation
(free class binder / disk memory), the disk-flat refutation, the
pcls-arity gap.  Plus the constructive results: the spike's parity
numbers, the device-epoch acyclicity route, the equation-free
reflective batching interface, the fulfil-time class pinning.  `git log
--oneline b9efdfc8..HEAD` is the stage-by-stage record; every commit
message carries its stage's findings.
