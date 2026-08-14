# The Layer-1 fabric generalization — worklist (mini-M5)

**Status (2026-08-14): PLANNED, design analysis done (orchestrator).**
The event-language spike PASSED
([`weak-memory-event-lang.md`](weak-memory-event-lang.md)); its one
architectural debt is the S2 finding: `WeakPromise.wpcfg` has exactly two
shared components (image, log) and the real machine has a third — the
device fabric.  This effort generalizes Layer 1 (W1–W5) over a shared
fabric and re-lands the capstone on the event language: adequacy → φ →
exhibit → robustness, ONE machine, no seam.  After it lands we regroup
(then: the M4 leaf retarget with spec-preserving packaging; the RVWMO
axiomatization research track).

## THE DESIGN KERNEL — this is NOT mechanical threading

Two Layer-1 arguments silently rely on cross-agent COMMUTATION of state
steps, which a shared fabric breaks:

1. **The front-loading factorization** (`WeakPromiseFact`,
   `phases_ptraces`): after the promise phase, state steps of different
   agents commute (frozen log, own promises), which is what reorders a
   behavior into agent-contiguous phases and gives per-agent traces.
   With a shared fabric, device accesses of different agents do NOT
   commute.
2. **The W2 replay** (`WeakRobustSim`): the toposort replays memory
   events in any dependency-respecting order; device answers are values
   read from the fabric, so changing the cross-agent interleaving of
   device accesses changes program states (`ts_oblivious` covers
   timestamps, not device answers).

THE FIX, in both places: make the device order a first-class citizen.
- The trace representation gains a GLOBAL DEVICE-ORDER WITNESS (the
  behavior's total order on device-touching events, e.g.
  `pt_devs : list (agent * nat)` into the per-agent traces).
- The dependency graph gains **gdev edges**: the total chain over
  device-touching events per the witness.  All its edges are consistent
  with the behavior's temporal order (as are gdep2's), so acyclicity of
  the union is free; the toposort/cone closure then RESPECTS the device
  order, so every replay preserves the global device interleaving and
  hence every device answer.
- The simulation invariant (`qcfg`) carries the fabric as the FOLD of
  processed device events; the factorization keeps device steps on the
  globally-ordered spine instead of reordering them agent-contiguous.
- NOTE the cone-cut lemma family ("cross edges emanate from fulfils")
  does NOT survive gdev edges (their sources are silent device steps) —
  and does not need to: that family served the DEAD lift; the exhibit's
  closure/toposort only needs downward closure + acyclicity.

The full machine's fabric semantics: `pstep` generalizes to
`P → D → wlabel → P → D → Prop` (the program step may move the shared
fabric; the promise arm moves no program, hence no fabric).  The event
language's `epf_step` becomes an INSTANCE of the generalized
`wp_pf_step` at `D := dev_state` — the definitional correspondence
completes, and the old per-hart-stream `pxv6` instance remains derivable
for the archive.

## Stages

- **G1 — the machine** (`WeakMem`/`WeakPromise`/`WeakPromiseFact` base):
  `wpcfg` gains a type parameter `D` + `pc_dev : D`; `wpstep`/
  `wp_pf_step` thread it through the generalized `pstep`; promise arm
  fabric-constant; basic lemmas re-threaded.  Keep Layer 1 dependency-
  free: `D` abstract, never `dev_state`, in these files.
- **G2 — factorization + traces** (`WeakPromiseFact`,
  `WeakRobustTrace`): the device-order witness in `ptraces`; the
  factorization re-proven with device steps on the ordered spine;
  `wp_behavior_traced`/`fulfil_once` variants.
- **G3 — the graph** (`WeakRobustGraph`/`Ord`): gdev edges; acyclicity
  of the union; closure/`anc` updated.
- **G4 — the replay** (`WeakRobustSim`): `qcfg` + fabric fold;
  `Qinv_step` device arms; the read/excl cruxes untouched (fabric
  orthogonal to timestamps); `sim_prefix`/`cone_Qinv` over the extended
  graph.
- **G5 — the composition** (`WeakRobustMain`/`WeakCompose` +
  `WeakEvPf`/`WeakEvAdequacy`): `robust_main` re-landed; `epf_step` as
  the `wp_pf_step` instance; ALSO (user-approved 2026-08-14): MERGE THE
  HART CONSTRUCTORS — one `Sail gen cpu (m : M unit) (fence)` replaces
  `ELoop`/`ECycle`, with the boundary rule
  `Sail (Ret tt) None ⟶ Sail (riscv_step tick) None (∃ tick)` and
  `Loop gen cpu := Sail gen cpu (Ret tt) None` as NOTATION (the
  boundary VALUE anchors the notation — `Ret tt` is unique since the
  result type is unit; the tick is chosen at the step).  The infinite
  CPU loop lives in the step relation + Löb, where nontermination
  belongs (an in-monad loop is impossible — `mchild_wf`).  Deletes one
  bookkeeping step per instruction and one corpse-arm family; the epf
  instance merges its boundary transition identically; THE NEW CAPSTONE — event-language adequacy
  + generalized Layer 1, end to end, `main_premises` consumed as today
  (the phase-2 exhibit-level discharge is a separate follow-on);
  `Print Assumptions` = the 5 rv64d axioms.
- **G6 — notes + audit**: WeakCompose §6 rewritten for the one-machine
  architecture; the S6/6c retarget note (WRITTEN FIRST, see below);
  lemma_diff justified; worklists updated.

Per-stage commits, tree green each time, findings in commit messages.
