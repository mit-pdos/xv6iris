# The Layer-1 fabric generalization — worklist (mini-M5)

**Status (2026-08-14): G1–G4, G5a/b/c1 and G6a LANDED.  G6b (the event
language as a Layer-1 INSTANCE, and the one-machine capstone) is NOT
delivered and is NOT deliverable as specified — see "G6 LANDED" at the
bottom: half of the G5c2 blocker (the free class binder) is CLOSED by
G6a's fulfil-time pinning, and the other half (the disk's flat memory) is
REFUTED, i.e. it cannot be closed by any change to `pstep`'s signature.
The successor effort must retarget, not retry.**
**UPDATE 2026-08-17: RETARGETED AND CLOSED by
[`weak-memory-soundness.md`](weak-memory-soundness.md) — the instance and the
one-machine capstone LANDED (`iris/WeakEvCapstone.xv6_ev_weak_robust`) once
the disk became a view-based agent (M5, `design/weak-memory-m5.md`).  This
file is now history + the G-series findings; move to `completed/` at the next
tidy.**
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

> **SUPERSEDED AS A PREMISE (A0′, 2026-08-17).**  `main_premises` no
> longer carries `dev_epoch_ok`: it is a per-agent DOMINATION condition
> and is REFUTED for ordinary xv6 bundles (`WeakRobustDisc` §A5).  The
> landed clause is `WeakRobustOrd.dev_wit_ok` — "the witness order is
> `gdep2`-consistent": no `gdep2` path from a LATER fabric access back to
> an EARLIER one.  That is EXACTLY what `gdep3` acyclicity needs, with no
> rank at all: `gdev` is the witness's successor chain, so splitting a
> `gdep3` cycle at its `gdev` edges leaves a `gdep2` run that walks the
> witness index back down.  New lemmas: `dev_wit_ok`, `dev_wit_ok_nil` /
> `_short` / `_devfree`, `dev_wit_ok_of_epoch` (the old premise implies
> the new one — everything below is still a SUFFICIENT condition),
> `tc_gdep3_wit` (the split), `gdep3_acyclic_at_wit` (pointwise, for the
> cone), `gdep3_acyclic_of_wit` (global).  Everything in this subsection
> stays in the file; only the premise moved.  See
> `design/weak-memory-premise-discharge.md` §2c "LANDED (A0′)".

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
  dev-free packaging.  (A0′: the fourth clause is now `dev_wit_ok`, and
  `Section exhibit`'s context variable with it — see the box in G5a.)
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

## G6 LANDED (2026-08-14) — a; and the REFUTATION that closes the effort

### G6a — THE CLASS IS PINNED AT FULFIL TIME (landed)

`WeakPromiseBridge.v`'s `Section bridge` gained a section parameter

```coq
Context (pcls : P → wlabel → wstate → wm_class).   (* retyped 2026-08-17 *)
```

and the promise-free fragment's two appending arms PIN the class they
stamp: `PFStore` has `k = pcls (pa_st ag) (LStore rl base data) (pa_ws ag)`
and `PFRmw` has `k = pcls (pa_st ag) (LRmw aq rl base tvs data) (pa_ws ag)`,
as the LAST premise of each.  So the applied forms are `wp_pf_step pstep
pcls …` / `wp_pf_run pstep pcls …`, with `pcls` in second position.  The
archive instantiates it at `WeakSailLTS2.lbl_class_p` throughout.

**THE SIGNATURE AS FIRST LANDED WAS ONE ARGUMENT SHORT (the finding; the
retype below fixed the TYPE, not yet the archive's class function).**
`pcls` was indexed by the LABEL and the `wstate` alone, but `WeakInterp.wm_class_of` branches on the ACCESS
KIND *first*, and the access kind is NOT in the label (`wlabel`'s
`LStore` carries only `(rl, base, data)`).  `WeakSailLTS`'s deltas
(e)/(e'') make an exclusive read open NO window and step an exclusive RAM
write as an ordinary `LStore`, so `amoswap.w.aq` — which xv6's `acquire`
executes — appends a message the interpreter classes `WCexcl` while
`lbl_class (LStore …)` can only be `WCrel`/`WCplain`.  Consequence: the
archived ⇒ bracket (`xv6_pf_instr` and the four statements under it)
carries a new side condition `WeakSailLTS.wrun_plainw` ("this run
appended no `WCexcl` message"), which is satisfiable but EXCLUDES EVERY
AMO.  **No capstone carries it** (the lift consumes the ⇐ direction), so
it costs no theorem — it is a coverage restriction on an archived
bracket, recorded at delta (e'').

**THE RETYPE LANDED (2026-08-17, follow-up commit).**  `pcls : P →
wlabel → wstate → wm_class` everywhere, and the argument is applied at the
FULFILLING agent's PRE-STEP program state: `PFStore` reads
`k = pcls (pa_st ag) (LStore rl base data) (pa_ws ag)` and `PFRmw` reads
`k = pcls (pa_st ag) (LRmw aq rl base tvs data) (pa_ws ag)`.
`cls_canonical clsf TS` is now `wm_ak m = clsf (pa_st ag) (ae_lb ev)
(pa_ws ag)` at the pre-record agent, and `pcls_obl` quantifies the program
argument (the equations hold for each fixed `p`); the replay hands the
acting agent its RECORDED `pa_st` verbatim, so `cls_canonical` +
`pcls_obl` + `replay_ws_relp` discharge exactly as before.  The archive is
instantiated at the PROGRAM-BLIND `WeakSailLTS2.lbl_class_p`
(`lbl_class_p _ l ws := lbl_class l ws`), so **`wrun_plainw` and every
other archive coverage restriction are unchanged** — the retype makes the
exact class function EXPRESSIBLE; supplying one is the separate step below.
Print Assumptions on the six capstones is byte-identical.

THREE PLACES WHERE THE ARGUMENT WAS NOT MERELY CARRIED, all forced by the
class now reading a state the surrounding lemma lets vary:
`WeakSailLTS`'s ⇒-bracket premise `Hpcls` became `∀ p, …` (the bracket has
no handle on the program state at the write node);
`WeakSailComplete.wp_pf_step_inv`'s re-take clause gained
`pcls (pa_st agd) l (pa_ws agd) = pcls (pa_st ag) l (pa_ws ag)`, because
its consumer `cfg_eqv` twins two REGISTER FILES and so changes exactly the
argument the class now reads (trivial at any program-blind class); and the
reverse bridge's `exec_cls_ok` is now indexed by the initial program list
`ps` (an `exec` records no program trace, and under `prog_free` no arm
moves a program state — `mstep_wp_pf_step` now returns that invariant).

**WHAT THE NEW ARGUMENT IS FOR (the SIGNATURE has landed; supplying the
exact class function has NOT).**  The access kind lives
there — the residual monad sits at the `MemWrite n req` node — so the
class function returns `wm_class_of (classify (WriteReq.access_kind req))
ws` at the `LStore` case (NOT by deferring to `lbl_class`, which
reproduces the bug — and which is exactly what the archive's
program-blind `lbl_class_p` still does, deliberately) and is then exact at
EVERY write; `wrun_plainw` disappears.  That is the remaining work, and it
belongs with the event-language instance (`pcls_ev`, soundness worklist
B2), not with the archive.  The replay is unaffected: `qcfg` hands the
acting agent the
RECORDED `pa_st` verbatim (only the `wstate` is retimed, and
`nproc done e.1 = e.2` makes it the very record `cls_canonical` speaks
about), so `cls_canonical` and `pcls_obl` merely carry the extra argument
along and the discharge is unchanged.  The same wall is waiting in
`WeakEvLang` (its plain `MemWrite` arm also accepts `ak_latest = true`),
so the change pays for itself twice.  **What NOT to do:** a
`sail_shaped`-style ∀-path monad predicate ("every RAM write this monad
reaches is plain") is REFUTABLE for the xv6 image — `classify` sends
`AV_exclusive`/`AV_atomic_rmw` to `ak_latest = true`, so the AMO and bare
`sc` paths in `riscv_step`'s decode tree refute it.  That mistake was
made and caught during G6a; it is the same genre as the
`oracle_consistent` post-mortem in `WeakCompose` §6(4).

**WHY AT THE FULFIL, AND NOT IN THE LABEL.** `pstep` emits a label and
never sees a `wstate`, so it cannot constrain the class itself — and a
free binder makes the pf machine a STRICT over-approximation of any model
that COMPUTES the class (the G5c2 finding, item 1).  The fulfil is the
only point where BOTH ingredients are in scope: the agent's `wstate`
(for `w_relp`) and the agent's program state (for the access kind).
Hence the arms, and not the label, carry the equation.

**HARDWARE CONTAINMENT IS PRESERVED — the PARM note's G6 addendum.**  The
class is our bookkeeping: no rule reads `wm_ak` (the rule-by-rule audit is
`WeakRetag`'s header), so pinning removes no hardware behavior — it
selects, among behaviors differing ONLY in an inert tag, the one the model
would have written.  Formally `wp_pf_step_rtc_wpstep` is unchanged: the
full machine's binder is free and accepts the pinned value, so every
containment statement proved against `wpstep` still covers the pinned
fragment.  Recorded as the G6a addendum in `WeakCompose` §6(5).

**DEVIATION, forced and recorded: ONLY the promise-free fragment is
pinned.**  The stage brief asked for `WeakPromise.wpstep`'s `WPFulfil` /
`WPRmw` to be pinned as well.  That is wrong, for a reason that only shows
up downstream: pinning the FULL machine makes `WeakRetag.wpstep_retag`
FALSE (a retagged run is not a run of a pinned machine), and the retag is
exactly what DISCHARGES `cls_canonical` today
(`WeakRetag.cls_canonical_canon`, consumed by
`WeakComposeLang.xv6_weak_robust_lifted`).  Pinning only the pf fragment
is also strictly better for every consumer: `pf_violation_free_hart`
quantifies over `wp_pf_run` ONLY, so the premise gets WEAKER (fewer runs
to rule out) and `robust_main`'s conclusion gets STRONGER (the exhibited
run is canonically classed).  Both directions move the right way.

**THE REPLAY'S NEW OBLIGATION, and how it is discharged.**  The exhibit
(`WeakRobustSim.Qinv_step`, `WeakRobustCone.Qcfg_step`) BUILDS pf steps
from a recorded trace, so it now owes `kc = pcls l ws_replay` at every
store/rmw it replays.  Two halves, both Layer-1 vocabulary, both now in
`WeakRobustTrace.v`:

- **`cls_canonical clsf TS`** (MOVED there verbatim from `WeakRetag`) —
  the RECORDED side: every logged message carries the class `clsf`
  computes at its fulfil event's pre-record agent state.
- **`pcls_obl clsf`** — the REPLAYED side: the class function must look at
  no timestamp.  It may look at the label's non-timestamp data and at
  `w_relp`, which is the ONLY `wstate` field the event fold computes from
  labels alone.  This is the exact analogue of `ts_oblivious` for `pstep`,
  and `WeakSailLTS2.lbl_class` satisfies it.

The bridge between them is `WeakRobustProv.w_relp_aevs_post_indep` (it
existed, unused, since W2b — it was written for exactly this and moved
down from `WeakRobustMain` so `WeakRobustSim` can see it) plus the new
`WeakRobustSim.replay_ws_relp`.  `sim_prefix`/`sim_full`/
`bad_edge_violates`/`robust_main`/`robust_transport` each gained
`pcls_obl pcls` and a per-bundle `cls_canonical pcls TS`; **`main_premises`
was NOT touched** — canonicity is discharged by the retag at the capstone,
obliviousness by the concrete class function, so neither is a new residue.

### G6a2 — THE DISK'S FLAT MEMORY: REFUTED, and it closes the effort

The stage brief's second half was "give the generalized `pstep` the flat
memory as an INPUT (`pstep : P → D → mem → wlabel → P → D → Prop`), the
machine passing `wflat (pc_img c) (pc_log c)`; the disk arm then takes the
REAL flat and delta (i) is deleted."  **That is not implementable, and the
obstruction is not a budget problem — it is the same one `lat_free_prog`
exists to name.**

**THE ARGUMENT.**  A flat-memory read is `latest_ts`-indexed: it reads the
TOP write to each byte of the WHOLE log (`WeakLang.wflat_lookup` states
exactly that).  That is the `lat = true` read shape, and Layer 1 excludes
`lat = true` from every robustness theorem by premise, because:

1. **The front-loading factorization breaks.**  `WeakPromiseFact.wp_swap`
   commutes a state step past a promise step by RE-APPLYING the very same
   `pstep` instance at the log with one more message appended.  It works
   only because `pstep` is log-blind, and its `lat_free l` side condition
   is there because `read_ok` at `lat = true` is the one memory-side
   condition an append can destroy (`read_ok_app` is stated at
   `lat = false`).  A flat argument is destroyed by an append for the same
   reason and with no side condition to hide behind, so `wp_swap`,
   `wp_front_load`, `wp_behavior_factor` and every traced-bundle theorem
   fail.
2. **The replay breaks, and G4's fabric treatment does not rescue it.**
   `qfab_step` replays a fabric-touching event at its RECORDED fabric
   because the `gdev` chain forces the witness order.  There is no
   analogue for the flat: the replayed log is `pf_log TS done`, a
   PERMUTED SUBSET (the cone cut drops messages), so the replay's flat is
   not the recorded one for any ordering discipline short of forcing
   every store into the device witness — which would chain all stores in
   behavior order, force π to the identity and make the robustness
   theorem vacuous.

**AND WIDENING THE OTHER SIDE IS NOT HONEST EITHER.**  The symmetric move
— widen `WeakEvLang.edisk_step` to accept the fictional memory, so the
over-approximating pf machine still lands inside the language — makes the
DISK THREAD'S WP obligation FALSE: with an arbitrary DMA source the burst
writes an arbitrary address set, which breaks the C/D/S protocol conjunct
of `weak_state_interp`.  The DMA's memory-faithfulness is LOAD-BEARING for
φ; it cannot be dropped, and Layer 1 has no vocabulary for it.

**SO delta (i) IS IRREDUCIBLE AT THIS LAYER**, and the G5c2 blocker
survives in exactly one arm.  The honest packaging for whoever picks this
up (design, not code — nothing was written):

```coq
(* the flat-faithful sub-relation of the instance's pf machine *)
Definition ev_pf_run_f c c' :=
  ∃ i l, wp_pf_step pstep_ev pcls_ev i l c c' ∧ ev_burst_faithful c i l c'.
(* THE ONE NAMED RESIDUE: the DMA over-approximation reaches nothing new *)
Definition ev_dma_harmless img d0 ps :=
  ∀ c, rtc (wp_pf_run pstep_ev pcls_ev) (wp_init img d0 ps) c →
       rtc ev_pf_run_f (wp_init img d0 ps) c.
```

`pf_violation_free_hart` over `ev_pf_run_f` IS derivable from
`weak_ev_pf_violation_free` (that is the ⇒ direction, now unblocked at the
class binder); `ev_dma_harmless` is what carries it to the full pf
machine.  It is a reachability-INCLUSION claim, so it is not refutable by
inspection the way a "the burst is memory-blind" premise would be, and it
joins the ledger next to `xv6_block_cover`.  **Do not state the seam as
"the burst holds at every memory" — that is refutable (`WDiskStepDma`
reads the descriptor chain out of `mv`), and this effort has already
burned three premises of that genre.**

**THE REAL FIX is architectural and belongs to M5, not here:** the DMA's
memory read must become a REAL machine read — a device-view read in a
machine that HAS device views — at which point the disk stops being a
program agent with a private oracle and delta (i) disappears with it.

### G6b — NOT DELIVERED (the instance and the one-machine capstone)

`epf_step` as a `wp_pf_step` instance, `weak_ev_pf_violation_free` in
instance form, and the new capstone were NOT built.  With G6a landed the
remaining work is well-defined and no longer blocked on a design question
except the disk arm above:

1. **`pexv6` needs the CPU** in its `PHart` constructor (the recorded
   cheap fix for the PLIC arm's hart index).  Trivial, no consumers yet.
2. **THE STANDALONE CONDITIONAL WRITE — solved by RETYPING `pcls`, which
   G6a did NOT do; do it first.**  The event language's plain `MemWrite` arm
   (`WeakEvLang.v` ≈ 345) accepts a conditional (`ak_latest = true`) RAM
   write and stamps `wm_class_of … = WCexcl`, so `elabel_ok`'s store arm
   is still existential in the class (`∃ k, …`).  Making it EXACT needs no
   language change and no side condition: `pexv6`'s `PHart` carries the
   residual monad, which at a store event sits at the `MemWrite n req`
   node, so — once `pcls` is retyped to `P → wlabel → wstate → wm_class` —
   `pcls (PHart m rs fn) (LStore rl base data) ws :=
   wm_class_of (classify (WriteReq.access_kind req)) ws` is exact, and
   `pcls (PDisk _) (LStore …) _ := WCplain` matches
   `WeakLang.wmsgs_of_map`'s stamp.  **Do NOT guard the arm with
   `ak_latest = false`** (that removes a real hardware behavior — the wrong
   direction for containment; the `MemRead` F6 guard already spends that
   coin once) **and do NOT add a `sail_shaped`-style ∀-path monad
   predicate** ("every RAM write this monad reaches is plain") — that form
   is REFUTABLE for the xv6 image, since `acquire` executes
   `amoswap.w.aq`.
3. Then `pstep_ev`/`pcls_ev`/`pdev_ev`, and the arm-by-arm factorization
   of `emonad_step` into "program part (monad + regs + fabric) × memory
   part (`elabel_ok`)".  This is the bulk: ≈20 arms, both directions.
4. Then the capstone, with `ev_dma_harmless` as its single new premise.

### G6c — the wrap (landed)

`WeakCompose` §6 is updated for what actually holds — NOT rewritten "for
the one-machine architecture", because that architecture is not the route
(G6b did not land).  Four edits: (2) records that the pinned class shrinks
`pf_violation_free_hart`'s quantification; **(3′) is NEW** — the
`cls_canonical lbl_class TS` conjunct `m6_side_conditions` gained, in the
same epistemic slot as (3) but one category better (a NORMALIZATION, and
the normalization is machine-checked, so `xv6_weak_robust_lifted` has no
such premise); (4) carries the G6a2 refutation in full, with the corrected
upgrade path and the warning not to state the seam as memory-blindness;
(5) carries the PARM-containment addendum plus the `wrun_plainw` coverage
restriction and the `pcls`-retyping fix.  The durable half of the finding
— **Layer 1's `pstep` is LOG-BLIND, and that is load-bearing** — is lifted
into `design/weak-memory-m6-robustness.md` §10.

**Audit at the G6 landing.**  Full `make -f CoqMakefile -j24 -k` green
(exit 0, zero `Error` lines).  `Print Assumptions` over the same 15
lemmas as at G5, with the same result: `gdep3_acyclic_epoch`,
`robust_main`, `bad_edge_violates`, `xv6_weak_robust`,
`xv6_weak_robust_prefix` CLOSED under the global context; the ten
model-facing ones (`xv6_weak_robust_lifted`, `xv6_weak_robust_adequate`,
`weak_ev_pf_violation_free`, `ewp_eloop`, `ewp_ev_ret`,
`ewp_ev_seq_ret`, `ewp_ev_started_set`/`_load`/`_fence`/`_wait_seq`) on
EXACTLY the five rv64d axioms.  `tools/lemma_diff.py --ref HEAD`: 9 items,
all pure RELOCATIONS (`cls_canonical` → `WeakRobustTrace`, the eight
`w_relp_*` → `WeakRobustProv`), each verified present in its new home.
No `Axiom`, no `Admitted`, no `admit`.  16 `.v` files touched, no file
added, nothing committed.
FOLLOW-ON TRACKS, unchanged in priority: the M4 leaf retarget with
spec-preserving packaging; the RVWMO axiomatization research track; phase-2
`main_premises` discharge (the static site checker of §6(3)).

### The G-series findings list (the durable part of this effort)

- **G3 — W7 REFUTED.**  In a promising machine an `rf` edge may point
  BACKWARDS in behavior time (a read reads a promise its author fulfils
  later), so no behavior-order rank makes `gdep2` monotone and
  union-acyclicity is NOT free.
- **G5a — THE DEVICE EPOCH.**  `depoch` + the per-edge residue
  `dev_epoch_ok` (no `rf`/`gE` edge lowers the epoch) closes `gdep3`
  cone-acyclicity; free at the empty witness; irreducible (the
  counterexample is a promise read across a device access).
- **G5c2 — the pf machine OVER-APPROXIMATES a computed-class model** at
  the free class binder, the disk's existential memory and the PLIC hart
  index.
- **G6a — CLASS PINNING**, at FULFIL time, in the PROMISE-FREE fragment
  only (pinning the full machine would falsify `WeakRetag`'s retag, which
  is what discharges canonicity).  Landed at
  `pcls : wlabel → wstate → wm_class`, which is ONE ARGUMENT SHORT: the
  class branches on the ACCESS KIND, which lives in the monad node and not
  in the label, so the archived ⇒ bracket lost AMO coverage
  (`wrun_plainw`).  The successor stage must retype it to
  `P → wlabel → wstate → wm_class`.  Any ∀-path monad predicate offered as
  a substitute is REFUTABLE for the xv6 image.
- **G6a2 — THE DISK'S FLAT MEMORY IS A LATEST READ**, hence irreducible at
  Layer 1: `wp_swap` and the cone replay both re-apply a recorded `pstep`
  instance at a DIFFERENT log, and only a log-blind `pstep` survives that.
  Widening the language instead falsifies the disk thread's WP.
