# The Layer-1 fabric generalization — worklist (mini-M5)

**Status (2026-08-14): G1–G4 landed; G5a/G5b/G5c1 landed (see "G5 LANDED"
at the bottom — the acyclicity route is the DEVICE EPOCH); G5c2/G5c3
BLOCKED on a Layer-1 signature finding that G6 must design around; G6
open.**
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
  - **G3 FINDING (2026-08-14), and it moves work into the Acyc band.**
    The union's acyclicity is NOT free and NOT derivable from `gdep2`'s
    plus temporal consistency, so no `W7` global-behavior-order clause
    was added (it would have bought nothing): in the promising machine an
    **rf edge may point BACKWARDS in behavior time** — a read may read a
    promise its author fulfils later, which is the whole point of
    promises — so no behavior-order rank makes `gdep2` monotone, and
    `gdep2`-acyclic + a `gdev` chain genuinely admits a mixed cycle
    (`e1 --gdev--> e2 --grf--> e1`).  What `WeakRobustOrd` supplies
    instead is (a) the rank CRITERION `gdep3_acyclic_of_rank`
    (`gdep2 ⊆ rk-nondecreasing` + `gdev ⊆ rk-increasing` + `gdep2_acyclic`
    ⟹ `gdep3_acyclic`), whose `gdep2` premise names exactly the
    compatibility the acyclicity band now owes, and (b) the instances
    that discharge it outright: `gdep3_acyclic_same_agent` (a witness
    that never crosses agents adds nothing — W3 already makes such a
    `gdev` edge a `gpo` edge) and `gdep3_acyclic_devfree` /
    `gdep3_acyclic_nodev` (no device events / empty witness), which is
    what every current consumer runs at.  **G5 must therefore re-land
    `WeakRobustAcyc2`'s walk over `gdep3`, or discharge the rank premise
    from the discipline** — `sim_full`/`sim_prefix` now take
    `gdep3_acyclic`.

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

## G5 LANDED (2026-08-14) — a, b, c1; c2/c3 BLOCKED, see the finding

### G5a — the acyclicity route that worked: THE DEVICE EPOCH

Preference (1) of the stage brief, with the residue NAMED per-edge rather
than assumed globally (so route (3) was not needed).  In
`WeakRobustOrd.v`:

- **`depoch DS e`** — the DEVICE EPOCH of an event: the witness position
  just past the LAST fabric-touching event of `e`'s OWN AGENT at or
  before `e` in that agent's trace (`dep_go`, a fold over `pd_ord DS`).
- **`depoch_gpo_le`** — a `gpo`-later event has epoch ≥.  NO hypothesis:
  the defining predicate is monotone in the trace index.
- **`depoch_dev` / `depoch_gdev_lt`** — a LISTED event's epoch is EXACTLY
  `S` its own witness index (the upper bound is (W3), the witness
  refining each agent's trace order), so `gdev` raises it by one.  This
  is the brief's "gpo-adjacency bridged by per-agent monotonicity", and
  it is a theorem, not a premise.
- **`dev_epoch_ok TS DS`** — THE NAMED RESIDUE: no `grf` and no `gE` edge
  LOWERS the epoch, i.e. no reads-from runs backwards ACROSS A FABRIC
  ACCESS.  Per-edge, no cycle quantifier — the epistemic shape of
  `rf_edges_ok`/`ee_ok`, and strictly weaker than the refuted W7 ("rf is
  forward in behavior time"): it only forbids an inversion that crosses a
  device access.  `dev_epoch_ok_nil` makes it free at the empty witness,
  so every dev-free consumer is unaffected.
- **`gdep3_acyclic_epoch`** (global) and **`gdep3_acyclic_at_epoch`**
  (POINTWISE: an event off every `gdep2` cycle is off every `gdep3`
  cycle) — the latter is what the exhibit's cone consumes, since the
  exhibit has no global acyclicity to spend.  `tc_gdep3_epoch` is the
  shared split.

**WHY THE RESIDUE CANNOT BE DISCHARGED (the G3 finding one level down).**
An `grf` edge genuinely may lower the epoch, and nothing in the bundle
forbids it.  The refutation, recorded at the definition:

```
D₁ (agent A, witness index 10) --gpo--> w (agent A, a fulfil)
w --grf--> r (agent B) --gpo--> D₂ (agent B, witness index 3)
D₂ --gdev⁺--> D₁                              (3 < 10)
```

is a `gdep3` cycle with an ACYCLIC `gdep2` and all of (W1)–(W4)
satisfied.  The witness order is the behavior's temporal order, so the
`gdev` chain says only `D₂ < D₁` in time, hence `r < D₂ < D₁ < w`; and
`r` reading `w`'s message BEFORE `w` executes is precisely a read of a
PROMISE, which the front-loaded promise phase supplies.  Note the "device
events are silent" hypothesis the brief offered does NOT help: the
inverting edge is between two MEMORY events.  So the epoch is where the
gap is smallest, and the gap is exactly `dev_epoch_ok`.

### G5b — the exhibit/composition over the real witness

`WeakRobustMain.v` rewired off the empty-witness instantiation:

- `Section cone` / `Section exhibit` take `DS`, `ptraces_wit TS DS`,
  `pd_init DS = d0`, `dev_epoch_ok TS DS`; the cone `Ucone`/`ancr`/
  `Rcone`/`cone_Qinv` are over `gdep3` (so gdev-predecessors are in the
  cone, which is what `Qinv_step`'s predecessor hypothesis demands).
- `gdep2_acyclic_main` unchanged; NEW `gdep3_acyclic_main` = it + G5a's
  rank.  `robust_main` now feeds `sim_full` the REAL witness.
- `robust_main` / `robust_transport` LOSE the `(∀ p l p', pdev … = false)`
  scope premise and take the package per `(mid, TS, DS)` through
  `ptraces_dev_of` (via `wp_behavior_fulfil_once_dev`).
- `main_premises nh TS DS` = `edges_split ∧ bad_wf ∧ ee_ok ∧
  dev_epoch_ok ∧ ∃ sync, ptraces_bytes_ok`; `main_premises_nil` is the
  dev-free packaging.
- **DEVIATION (forced, recorded at the definition):** `bad`'s
  "no publishing ancestor" conjunct, and `bad_min`, are over `gdep3`, not
  `gdep2`.  The exhibit replays the `gdep3` cone, so the ¬pub arm finds
  its publishing fulfil in the `gdep3` ancestry; quantifying the conjunct
  over `gdep2` would leave that arm unusable.  It STRENGTHENS `bad`,
  hence `edges_split`; at the empty witness `gdep3` IS `gdep2` and
  nothing moves.  `bad`/`bad_min`/`bad_wf`/`edges_split`/`main_premises`
  all gained the `DS` index; `bad_wf_strong`/`gdep2_acyclic_bad_free`
  too.
- The cone-acyclicity family (`rf_edges_ok_on_min`, `anc_mr`,
  `cone_acyc2_of_min`, `cone_acyc_of_min`) moved OUT of the section to
  TOP LEVEL with named binders, plus dev-free corollaries
  (`cone_acyc_of_min_nil`, `cone_Qinv_nil`, `tc_gdep3_nil`), because both
  the witness route and the archived route (`WeakRobustCone`,
  `WeakSailCone`, `WeakComposeLang`) name them and section discharge made
  their argument lists depend on which variables a proof happened to use.
- Archived route kept compiling at `PDevs d0 []` / `PDevs tt []`;
  `WeakComposeLang.tb_facts` gained a `DS` parameter.

### G5c1 — the user-approved Sail constructor merge (LANDED)

`WeakEvLang.eexpr` now has ONE hart constructor
`Sail (gen) (cpu) (m : M unit) (fn : option …)`; `ELoop gen cpu` and
`ECycle gen cpu m fn` are transparent DEFINITIONS (`ELoop` a Definition
rather than a Notation because `epower_fork` applies `ELoop gen` to one
argument).  Fallout:

- `emonad_step`'s `Ret` arm IS the boundary rule now
  (`∃ tick, e' = Sail gen c (riscv_step tick) None ∧ σ' = σ`): the old
  "pop to `ELoop`, then fetch" is ONE step.  `eprim_step` has five arms,
  one hart arm, ONE corpse arm.
- Every inversion lemma keeps its statement VERBATIM
  (`eprim_step_loop_inv`, `eprim_step_cycle_inv`, …); only the proofs
  moved.  `ewp_ecycle` / `ewp_eloop` (the RESTART rule) unchanged.
- **The one statement that had to move:** `ewp_ev_ret` and
  `ewp_ev_seq_ret` LOSE their `▷`.  `ECycle gen c (Ret u) None` IS
  `ELoop gen c` (the result type is `unit`), so there is no step left to
  strip; `ewp_ev_ret` is now the conversion and the real rule is
  `ewp_eloop`.  Three `iNext`s deleted in `WeakEvStarted`; all the
  started-handshake and composition lemma STATEMENTS are unchanged.

### G5c2/c3 — BLOCKED, and the block is a finding G6 must design around

`epf_step` CANNOT be exhibited as an instance of `wp_pf_step` in the
direction the capstone needs.  ⇐ (every `epf_step` is a `wp_pf_step` of
the instance) is fine and is the definitional correspondence; the
capstone needs ⇒ — every `wp_pf_run` of the instance is an `epf_run` —
because `pf_violation_free_hart` quantifies over ALL pf runs, and it
fails at THREE points where `wp_pf_step` is a strict OVER-approximation
of what the language can do:

1. **The message CLASS is a free binder.**  `PFStore`/`PFRmw` quantify
   `∃ k, … WMsg base data (Some i) k`, while the language COMPUTES it
   (`WeakInterp.wm_class_of ak ws` at the storing hart's own `wstate`).
   `cls_of`/`pub_of`/`violation_hart` are all class-sensitive, so the pf
   machine reaches violating logs the language cannot produce.  `pstep`
   cannot constrain it: the class is neither in the label nor derivable
   from the program state (it reads `w_relp`, a `wstate` field).
2. **The disk's DMA reads the flat memory.**  `edisk_burst` runs
   `wdisk_step (wgdev σ) (wflat (wgimg σ) (wglog σ)) d' w`; `pstep` has
   no memory argument, so the arm has to be existential in `mem` —
   exactly the archived route's recorded delta (i)
   (`WeakCompose.pstep_xv6`'s disk arm).
3. **The PLIC arm needs the target hart's INDEX** (`dev_seip (wgdev σ)
   (fin_to_nat c)`) and `pstep` has none.  This one is CHEAPLY FIXABLE —
   put the `CPU` in `pexv6`'s `PHart` constructor — and is recorded only
   so it is not rediscovered.

So the S2 "zero glue premises" claim survives at `epf_run` and does NOT
survive the move to `wp_pf_run` at any Layer-1 instance: the glue that
re-enters is the SAME pair the archived route already names (class
canonicity — `WeakRetag.cls_canonical` — and the DMA's memory argument).
NOTHING was forced: no capstone was written, no premise invented.

**WHAT G6 OWES.**  Either (a) make the class an OUTPUT of the program
step (widen `wlabel`'s store arm or `pstep`'s signature) so the pf
machine cannot pick it, and give the disk arm its memory — i.e. a Layer-1
signature change, the natural successor to the G1 fabric change; or (b)
relativize `pf_violation_free_hart` to the pf runs the EXHIBIT actually
builds (whose classes come from the behavior's own log, which is what
`cls_canonical` says), which is a `WeakRobustMain` change and keeps
Layer 1's signature; then finish G5c2/c3.  Plus the original G6 list
(WeakCompose §6 rewrite, the S6/6c retarget note, worklists).

**Audit at the G5 landing.**  Full `make -f CoqMakefile -j12 -k` green.
`Print Assumptions` over 15 lemmas — `gdep3_acyclic_epoch`,
`robust_main`, `bad_edge_violates`, `xv6_weak_robust`,
`xv6_weak_robust_prefix` CLOSED under the global context; the ten model-
facing ones (`xv6_weak_robust_lifted`, `xv6_weak_robust_adequate`,
`weak_ev_pf_violation_free`, `ewp_eloop`, `ewp_ev_ret`,
`ewp_ev_seq_ret`, `ewp_ev_started_set`/`_load`/`_fence`/`_wait_seq`) on
EXACTLY the five rv64d axioms: `rv64d.valid_reservation`,
`rv64d.plat_term_write`, `rv64d.match_reservation`,
`rv64d.load_reservation`, `rv64d.cancel_reservation`.
`tools/lemma_diff.py --ref HEAD`: CLEAN.  No `Axiom`, no `Admitted`.
