# Shrinking the capstone's premise ledger — worklist

**STATUS UPDATE (2026-08-14): SUPERSEDED-PENDING-SPIKE.**  The
premise-elimination approach did not converge (the user's call, and
right): the ledger changed shape without shrinking, because every glue
premise was a shadow of the two-machine granularity mismatch.  The plan
of record is now the EVENT-GRANULAR LANGUAGE
([`../design/weak-memory-event-granular.md`](../design/weak-memory-event-granular.md),
spike: [`weak-memory-event-lang.md`](weak-memory-event-lang.md)), under
which the C-series artifacts (shape towers, axiom records,
`rv64d_live_residue`, Hcq/Hseip/Hpriv, cone_liftable, the retag) are
DELETED rather than proven.  This file is kept as the FAILURE RECORD —
the ten findings and the stage notes below are the evidence base for the
new design.  Phase 2 (exhibit-level discharge of `main_premises` from
per-site WWP tokens) SURVIVES the pivot and remains the discharge plan
for the one genuine premise family.  Do further work here ONLY if the
spike hits a named fail criterion.


## C9 (LANDED 2026-08-14): the state-conditioned liveness — THE LAST
## PREMISE IN SCOPE.  BOTH HALVES OF SEAM (6) ARE NOW THEOREMS.

`∀ b, sail_live (riscv_step b)` is **deleted from the tree**, predicate
and all, and replaced by

    WeakShapeLive.riscv_step_live_ax :
      rv64d_live_residue → ∀ rs b, priv_ok rs → sail_live_st rs (riscv_step b)

with `Hpriv` (every hart record's `cur_privilege ∈ {M,S,U}`) as the new
third conjunct of `xv6_cone_premises`.  Both capstones take the two
RECORDS (`rv64d_axiom_shapes`, `rv64d_live_residue`) and are still at
exactly the five rv64d axioms.

### The predicate, and the two arms that are NOT concrete

`WeakSailComplete.sail_live_st rs m` (§2, notes (f)/(g)) — `RegRead`
answered `k (register_lookup r rs)`, `RegWrite` THREADING the state
(`sail_live_st (register_set r v rs) (k tt)`), memory arms unchanged
(the C2/O1 narrowed answers), `ExtraOutcome`/`GenericFail`/`Discard`/
`ChooseReal` refused.  Two arms stay quantified and each is forced:

- **memory** — the completion's freedom; the LTS picks the value.
- **`sig_seip`** — and this one is the design point.  `irq_deliver` is
  an arm of the SAME LTS and it writes the pin **without moving the
  residual**, so a residual whose liveness depended on the pin would
  lose it at a delivery and `WeakSailCone.res_ok_frame` would be false.
  Answering that ONE register with `∀ v` makes liveness invariant under
  any pin write (`sail_live_st_agree` over §9.1's `regs_agree seip_reg`,
  then `sail_live_st_seip`), which is exactly the closure the LTS asks
  for.  **THE RULE: a predicate over a per-agent state must be
  ∀-quantified in exactly the components another agent can write.**
  Nothing else needs it — the pin is the only register any other agent
  touches.

### THE INVARIANT SHAPE THAT WORKED (the thing to reuse)

`live_res p := match sp_m p with None => True | Some m =>
sail_live_st (sp_regs p) m end` — **live at the record's OWN
registers**, and `res_ok` is that conjoined with `sail_shaped m`.  It is
inductive step for step because every `sail_mstep` arm moves `sp_regs`
exactly as `sail_live_st` threads it:

| arm | registers | why it goes through |
|---|---|---|
| `RegRead` | unchanged | both branches of the predicate give `k (register_lookup r rs)` (`sail_live_st_regread`) |
| `RegWrite` | `register_set r v rs` | the predicate's own arm |
| fused rmw | `rs → rs1` across the whole `silent_run` | `sail_live_st_silent1` is stated over the PAIR (`sail_live_st b.2 b.1`), so the window carries the state with it |
| parked fence | unchanged | `res_ok_frame` |
| `irq_deliver` | `register_set sig_seip v` | `res_ok_irq`, from the pin frame above |
| BOUNDARY | unchanged; residual := `next tick` | `riscv_step_live_ax` at THOSE registers, under `Hpriv` |

**A mid-instruction privilege write costs nothing.**  Trap entry sets
`cur_privilege` inside the monad; the residual after it is measured at
the state the write produced, so no side condition is needed and
`priv_ok` is NOT required to hold mid-instruction — only at boundary
records, which is what `Hpriv` says.  The two readings that do NOT work
and are worth naming: a record-INDEPENDENT one ("live at every state")
is the refuted `∀ b` again, and one pinned to the BLOCK's entry state
does not survive the first `RegWrite`.

### `priv_ok`, final contents

    priv_ok rs := register_lookup cur_privilege rs ∈ {Machine, Supervisor, User}

and **nothing else** — the sweep was not run (below), so no site forced
a second conjunct.  Any site the sweep later finds to need more state
gets ADDED here with its reason, per the design.

### The kit: `WeakShapeLive.v`

`gliveP Q P rs m` — `gpost` with the memory/barrier arms opened up and
the register state threaded, and with a **postcondition over the FINAL
STATE** (`Ret x ↦ P x rs`).  That CPS shape is forced: at `bind m k` the
state `k` starts in is path-dependent (whatever `m`'s `RegWrite`s left),
so the only compositional rule is `gliveP_bind`, "the prefix's
postcondition is the continuation's hypothesis" — the same driver shape
as `DecodeSetU.goodbP`, which is the recorded porting recipe applied in
the other direction (this IS the state-pinned traversal; `WeakShape.glive`
is its register-free specialisation).  `glive_st rs m` is the
information-free instance; `glive_st_sail_live_st` is the bridge, and
`glive_glive_st : glive true m → glive_st rs m` is the **register-free
tower reuse** (a prefix that never branches on a register is live at
every state).  Kit: mono / ret / returnm / bind / bind0 / the failure
leaves / throw / assert_exp(') / `gliveP_read_reg`(`_ne`) /
`gliveP_write_reg` / `gliveP_try_catch` / `gliveP_liftR` /
`gliveP_catch_early_return`.

### THE SWEEP WAS NOT RUN, AND ITS SIZE IS NOW MEASURED

`tools/gen_shape.py --mode live` (`make live-sites`) is the enumerator —
**a report, not an emitter**, because `glive_st` is FALSE at any function
with a reachable failure node, so a blind tower would be hundreds of
unprovable lemmas.  Measured on this model:

    reachable from try_step: 1053 (monadic 345)
    monadic defs with a DIRECT failure site:  123
    monadic defs whose CONE carries one:      302
    monadic defs whose cone is failure-free:   40
    sites by kind: assert_exp=187  exit=130  internal_error=107
                   reserved_behavior=4  throw=4  untilMT=3

i.e. **431 sites, not "~100"** — (O3)'s estimate was low by 4×.  The
per-function table is in the tool's output; the headline entries are
`encdec_forwards` (71+71), `assembly_forwards` (15+15), `pmaCheck`
(10 assert + 4 internal_error), `trap_handler` (7), `check_PTE_permission`
(8), the three `untilMT` loops (`checked_mem_read`/`_write`,
`mem_write_ea`), and `try_step` itself (3 `assert_exp` + 1
`internal_error`).  The 40 failure-free functions are printed with their
skeletons, which is where an emitter would start; `gl_solve` does not
exist yet and writing it is the sweep's first task (the (O8)/(O11)
discipline applies verbatim — gate the leaf on an ATOMIC goal,
`Hint Constants Opaque`, name every callee in a hand script).

So the residue is **hypothesis-ized as a named record**, per the stage's
own fallback:

    Record rv64d_live_residue := {
      rlr_try_step : ∀ n b rs, priv_ok rs →
          gliveP (λ _ _, False) (λ _ rs', priv_ok rs') rs (try_step n b);
      rlr_tick_clock : ∀ rs, priv_ok rs → glive_st rs (tick_clock tt) }.

`rlr_try_step`'s POSTCONDITION is `priv_ok` again — an instruction may
change `cur_privilege` and what the model guarantees is that it lands in
one of the three; carrying it is what lets the `tick_clock` tail be
discharged at the state `try_step` left, and it is the same statement
`Hpriv` makes per record, so **a proof of one is most of a proof of the
other**.  `rv64d_axiom_shapes` was NOT extended with liveness fields:
with the whole cone hypothesised, the three opaque axioms' liveness sits
INSIDE `rv64d_live_residue`, and adding unusable fields to the shape
record would misreport what is assumed.

### THE SWAP IS NOT A WEAKENING — direction verified, and it matters

The deleted `∀ b, sail_live (riscv_step b)` is UNSATISFIABLE, so it
formally implies anything, including the record.  But `Hpriv` is a NEW
per-trace obligation the old premise did not imply.  What the swap buys
is not a smaller ledger, it is a NON-VACUOUS capstone: a supplier who had
"discharged" the old premise had discharged nothing.  Recorded in
`WeakComposeLang` §D 1 in as many words.

### Deleted, and why (lemma_diff justification)

`WeakSailComplete.sail_live` (the ∀-form `Fixpoint`), `sail_live_choose`,
`sail_live_silent1`, `sail_live_silent_run` — superseded by their `_st`
forms; nothing needs the ∀-form, so per the guiding principle it is gone
rather than kept beside its replacement.  `WeakShape.glive_live` →
`glive_sail_live_st` (the ∀-form implication, which is what survives as
the register-free reuse).  `wr_node_live` and `gok_stageC` and
`WeakShapeTop.riscv_step_ok_cone` are RESTATED (extra `rs` parameter),
not deleted.  `WeakShape.glive`/`gok` are KEPT: `glive true` is still
the cheap route wherever a fragment is register-insensitive.

## END STATE (after C9) — THE EFFORT'S IN-SCOPE LEDGER IS EMPTY

Every premise this effort set out to eliminate or reduce has been.  What
`WeakComposeLang.xv6_weak_robust_lifted`/`_adequate` now assume:

| premise | status |
|---|---|
| `rv64d_axiom_shapes` | IRREDUCIBLE (3 opaque monadic `Axiom`s of the model).  Only alternative: define them in `model-xv6iris/riscv_extras.v`, which moves the same assumption into the model.  Decide deliberately. |
| `rv64d_live_residue` | A WORK ITEM: the (O3) liveness sweep, un-run, sized above. |
| `Hcq ∧ Hseip ∧ Hpriv` (`xv6_cone_premises`) | per-image checker facts.  `Hpriv`'s upgrade path = the model-level reachability invariant `priv_ok` is `riscv_step`-preserved (same sweep as the record). |
| `main_premises`, `cone_liftable`, `img_total`, the fresh era, the WP package, the 5 rv64d axioms | NOT IN SCOPE by charter — discharge campaigns (static checker, Iris discipline exports, 6c pinnedness, M5). |

**This file should move to `completed/`** on the next pass over the
notes (it was left in `projects/` by the C9 task).

**Status (2026-08-14): C9 LANDED; the in-scope ledger is closed (stage C8 had
landed (O10)'s specification fix, the kit collapse, the memory cone, and the
SHAPE capstone swap; C9 restated and closed the LIVENESS half).**  Follow-on to
[`completed/weak-memory-lift.md`](../completed/weak-memory-lift.md):
eliminate or reduce the premises of
`WeakComposeLang.xv6_weak_robust_lifted`/`_adequate` that are provable
rather than assumable.  Ordered by the assessment (elimination first,
coverage fixes second, model-level sweep third; the genuine robustness
conditions — `edges_split`/`ee_ok`/`bytes_ok`/`bad_wf`/`Hcq` — and the
MMIO seam (`cone_liftable`) are NOT in scope: they are discharge
campaigns (static checker + Iris discipline exports + 6c pinnedness,
M5), not eliminations.

## The elimination facts

- **`Hcls` is eliminable with NO machine change**: `wpstep` never reads
  `wm_ak` (the class enters as `WPPromise`'s free binder; fulfil only
  matches the log entry; `store_post_run` takes `rl`; `read_ok`/
  `excl_ok` ignore it), so every behavior retags to a class-canonical
  behavior with identical program states, wstates and flat memory, and
  the capstone's conclusion is class-independent.  Retag classes to
  `lbl_class` at each message's (exactly-once, by
  `wp_behavior_fulfil_once`) fulfil pre-record.
- **`Hres` is a derivation, not an assumption**: the preservation
  lemmas already exist (`WeakSailComplete.sail_shaped_res_step`/
  `sail_live_res_step`/`oracle_consistent_res_step`; `irq_deliver`
  preserves all three).  Thread along traces from block starts; the
  residue is the base case = `∀ b, sail_shaped/sail_live (riscv_step b)`
  (group 3) + block-start stream consistency (`Horc`, which is the
  MMIO-seam family and replaces `Hres` as the smaller premise).
- **`Hirqb` is a COVERAGE GAP** (hardware asserts SEIP mid-instruction;
  the premise excludes those behaviors).  Fix: keep mid-block
  deliveries inside the hart segment and commute them FORWARD past the
  rest of the block on the wl side, sound when the delivery's residual
  never `RegRead`s `sig_seip` (`seip_free`, a quiet_tail-style
  Fixpoint) — via a register-frame simulation over `seip_free` monads
  (runs from `rs` and `register_set sig_seip v rs` produce the same
  labels and final states agreeing off `sig_seip`).  Replaces `Hirqb`
  by the strictly weaker `Hseip` (mid-block deliveries have seip-free
  residuals).  RECORDED NARROWING: the remaining excluded corner is a
  mid-block delivery landing between an SIE-on interrupt check and an
  in-block sip read — kernel sip reads run with SIE off (trap context),
  so the per-image discharge is a checker fact; the delivery-BEFORE
  placement (sound when the check is seip-insensitive, i.e. SIE off)
  can close it later if wanted.
- **Group 3 (`∀ b, sail_shaped/sail_live (riscv_step b)`) is a
  model-level truth**, not WWP-derivable (traces include arbitrary
  user code no WP covers).  Route: compositional mode-indexed shape
  typing over the Sail combinator vocabulary (bind/returnm/exceptions/
  foreach/mem wrappers), typeclass-driven so the search walks the
  generated code; manual instances only at the exclusive-window sites
  (lr/sc, AMOs, `update_and_write_pte`).  Not a vm_compute checker —
  `∀ r` continuations over `bv` cannot be computed through.

## FINDING (2026-08-13): the ∀-path oracle premise is UNSATISFIABLE —
## `Horc` is not to be proven, it is to be DELETED

`oracle_consistent`'s RAM-read arm quantifies over every read value —
including the FETCHED WORD (ifetch is a plain RAM read) and every
page-walk PTE value.  One positional stream must therefore serve, from
one device state, every instruction any junk fetch decodes to along
every junk-but-valid-PTE translation path: two fetched words decoding
to `lw`/`lb` at the same VA, steered by the same junk PTE path to a
device address, demand the same stream head have length 4 and 1 —
contradiction; an empty stream fails on any junk path reaching a device
read.  So `∃ d, oracle_consistent d (riscv_step b) str` is FALSE at
essentially every S-mode record, for any stream: `Horc`, L2/L3's
`seg_hart` `Hoc`, and `cone_liftable`'s hart conjunct are
vacuity-making premises (a third finding of the false-premise genre,
present since L3).  Request-keyed entries cannot fix it — answer #2
depends on how request #1 evolved the device, i.e. on the path; the
only oracle that answers arbitrary request sequences is the device
automaton itself.

**Fix (stage D — LANDED 2026-08-13; replaces the old batch-B plan's seam
handling):**
`sp_dev : dstream` becomes a per-hart `dev_state`, served by TOTALIZED
`dev_read`/`dev_write` (unmapped device-range accesses return
junk-and-unchanged — the virtio lesson: model undefined device
behavior as "anything", never "nothing").  Then per-instruction oracle
consistency is definitionally true (`oracle_consistent`/`ocons_res`/
`Horc` deleted; `tail_complete`'s device arms non-stuck by totality),
and the retained MMIO assumption shrinks to its satisfiable core: the
hart's private fabric agrees with the wl fabric at each hart segment
(an equality conjunct in `wl_lift`'s SegHart, twin of the disk's
`wa_dd u = wgdev g`).  Ripple: WeakSailLTS (psail + sail_mstep device
arms), WeakSailLTS2 (delete oracle_consistent; sail_block_wrun's Hoc
becomes fabric agreement), WeakSailComplete (ocons_res gone),
WeakSailCone (Hres derivation loses its oracle conjunct),
WeakComposeLang (hag/wl_cfg carry the fabric; cone_liftable
restated), WeakCompose §6 (4) prose.

**How it landed, and the one shape worth reusing.**  The ⇒ bracket lost its
existential stream outright: the agent now starts at `wm_dev s` and ends at
`wm_dev s'`, because a `wrun` can only take device accesses the PARTIAL
`dev_read`/`dev_write` accepted, so the totalized and partial answers
coincide there.  The ⇐ bracket keeps ONE side condition,
`WeakSailLTS2.dev_ok_blk next i c'` = "every configuration from which the
block reaches `c'` has agent `i`'s current monad node decodable by the
partial functions".  **INDEX A RUN-LOCAL SIDE CONDITION BY THE RUN'S TARGET,
NOT ITS SOURCE.**  Every peel of the unbracket induction hands back an `rtc`
to the SAME `c'`, so a target-indexed predicate is a CONSTANT of the whole
mutual induction and needs no threading at all; a source-indexed one would
have to be re-established at each step, i.e. every forcing lemma
(`block_forced_silent`/`_fence`/`_stuck`) would have to export the peeled
step.  Two things it must NOT be: a ∀-path predicate on the monad (same
unsatisfiability as the oracle — junk paths make device accesses of every
width), and a conjunct of `pf_solo` (WeakSailComplete's reader-tail
completion CONSTRUCTS `pf_solo` steps over an arbitrary residual and cannot
discharge it).

## Stages

- **A1 `WeakRetag.v`** — the retag simulation: `retag_log`,
  behavior-to-canonical-behavior (same prog/mem/wstates), trace
  transport (retagging preserves `atrace_wf`/`ptraces_of` — labels
  carry no classes), canonicity of the result (`Hcls`'s statement,
  proven).
- **A2 (WeakSailCone.v)** — `hres_of_horc`: `Hres`'s statement derived
  from group-3 facts + `Horc` (∀ boundary records, ∀ b,
  ∃ d oracle-consistent stream) + trace wf.
- **A3 (WeakSailComplete.v)** — the seip kit: `seip_free`, the
  register-frame simulation, delivery-forward-commutation for ni runs.
- **B (WeakSailCone.v + WeakComposeLang.v)** — segmentation
  generalization (mid-block deliveries inside SegHart, exported with
  their values + seip_free facts), the wl lift's deferred-delivery
  arm, and the capstone restatement: premises become
  `main_premises ∧ (Hcq ∧ Horc ∧ Hseip) ∧ cone_liftable` quantified
  over CANONICAL-CLASS bundles (retag precomposition), with group-3
  facts still `∀ b` hypotheses until stage C.
- **C1 (LANDED)** — `WeakShape.v`: the compositional kit.  `gwalk`
  unifies `sail_shaped`/`amo_tail` as ONE window-indexed walk (one
  lemma per combinator, not two); `glive` indexed by ExtraOutcome
  fatality; `gquiet` crosses exclusive windows at binds
  (`gwalk (Some _) (Ret _) = False` forbids carrying a window into a
  continuation).  Calibration: 1–3 s per generated function with
  `shape_solve`; the monolithic route measured (347 s, one unlocalised
  stuck goal) and rejected.  Call graph: 358 monadic defs reachable
  from `try_step`, 2 touching memory, 0 `ChooseReal`.

## FINDINGS (2026-08-13, C1 — machine-checked): BOTH stage-C goals are
## FALSE as stated, and the LTS has an exclusive-window coverage gap

- **(O1)** `∀ b, sail_live (riscv_step b)` is REFUTABLE
  (`WeakShape.read_ram_not_live`): `sail_live`'s memory arms quantify
  over every answer INCLUDING the abort `inr ab`, which `read_ram`
  maps to `exit tt` = `GenericFail`; `sail_mstep` only ever supplies
  `inl (w, None)` / `inl None`.  Fourth finding of the
  over-quantified-∀ genre.  FIX: narrow `sail_live`'s (and, for
  symmetry, `sail_shaped`'s) MemRead/MemWrite arms to the
  LTS-supplied answers.
- **(O2)** `∀ b, sail_shaped (riscv_step b)` is REFUTABLE: `amo_tail`
  demands a conditional write before `Ret`, but `execute_LOADRES`
  (bare `lr`), `execute_AMO`'s fault/mismatch arms and
  `update_and_write_pte`'s error arms abandon the window.  The LTS is
  also STUCK there (`sail_mstep` steps an `ak_latest` read only by
  fusion) — hardware executes bare `lr` and failing `sc`, so this is a
  MACHINE coverage gap, not just a predicate bug.  FIX (decided):
  (i) weaken `amo_tail`'s `Ret` arm to allow window abandonment while
  keeping "any conditional write is same-address/width"; (ii) ADD a
  bare-exclusive-read arm to `sail_mstep` (pf side only, like the
  totalization): the read steps as a PLAIN `LLoad` (lat := false —
  an abandoned reservation read has ordinary load semantics; the
  machine only GAINS behaviors, the safe direction).  The ⇐
  reconstruction gains a run-local side condition ("no bare exclusive
  reads in the block" — TARGET-INDEXED like `dev_ok_blk`, per the
  recorded lesson), joining the seam family; per-image discharge:
  kernel AMOs target mapped lock words and do not fault.
  `tail_complete` takes the bare arm at abandoned windows, restoring
  totality.
- **(O3)** liveness is NOT loop-compositional (`untilMT` guards end in
  `fail`), and ~100 `exit`/`internal_error`/`assert_exp` sites need
  reachability arguments — but ONLY for the liveness half; `gwalk` is
  immune (a `GenericFail` continuation is `False → _`).  So expect
  the `sail_shaped` sweep to be clean and the `sail_live` sweep to
  carry per-site reachability facts (same checker family as D-M6-8).

- **C2 (LANDED 2026-08-13)** — the spec fixes, all machine-checked, both
  capstones still at exactly the 5 rv64d axioms.  What landed:
  - **(O1)** `sail_shaped`/`amo_tail`/`sail_live` (and `WeakShape`'s
    `gwalk`/`glive`) quantify their `MemRead`/`MemWrite` arms over the
    answers `sail_mstep` supplies — `∀ w, P (k (inl (w, None)))` and
    `P (k (inl None))` — instead of the full answer type.  `quiet_tail`
    needed nothing (its memory arms are `False`).
    `WeakShape.read_ram_not_live` is false and deleted; `glive_read_ram`
    (the positive leaf, for the three read kinds the model produces)
    replaces it.
  - **(O2a)** `amo_tail`'s `Ret` arm is `True`.  Everything else it forbids
    stays (no `MemRead`, no `Barrier`, any `MemWrite` must be the closing
    conditional write, now with the narrowed continuation) — which is
    exactly what makes an abandoned tail steppable and barrier-free.
  - **(O2b)** the BARE exclusive-read arm, as a second disjunct of
    `sail_mstep`'s `LLoad` case.  **It brackets the whole abandoned window**
    (`silent_run … (Interface.Ret y, rs1)`, `p' = PSail (Some (Ret y)) rs1 …`)
    the way the fused arm brackets to its conditional write.  That shape
    was FORCED and is the key design point: a one-step bare arm would leave
    the hart in "window mode", where `sail_shaped` is not preserved and the
    conditional write has no LTS arm — `sail_shaped_res_step` and
    `tail_complete` would both have broken, and the residual invariant of
    the whole cone (`WeakSailCone.res_ok`) would have had to become
    window-indexed.  Bracketing to `Ret` keeps every residual invariant
    literally unchanged.
  - the ⇐ side condition is **`WeakSailLTS2.fused_blk next i c'`** =
    `∀ c1 c2, pf_solo next i c1 c2 → rtc (pf_in_block next i) c2 c' →
     pf_solo_f next i c1 c2`, with `pf_solo_f` = "a step from an
    `at_excl_read` configuration APPENDS a message" — label-free (the fused
    arm logs, the bare one does not), target-indexed exactly like
    `dev_ok_blk`, and NOT a conjunct of `pf_solo`.  It joins `dev_ok_blk` in
    `sail_run_wrun`/`sail_block_wrun`/`wprim_hart_block*` and in
    `WeakComposeLang.wl_lift`'s SegHart bundle.
  - `tail_complete` tries fused-if-available (`amo_reach` now returns
    "closes ∨ abandoned-at-Ret") and takes the bare arm otherwise; it
    EXPORTS which, as `∃ … (fu : bool), … ∧ (fu = true → rtc (pf_solo_f next i) c c')`.
    The quiet skeleton pays nothing for it (`pf_solo_q_f`: a quiet step is
    fused vacuously, since an exclusive-read node emits only `LLoad`/`LRmw`).
- **C2 FINDING (machine-forced): the KIT cannot follow the `amo_tail`
  weakening.**  Setting `gwalk (Some _) (Interface.Ret _) := True` REFUTES
  `gwalk_bind` and every loop lemma of `WeakShape` §5: in `bind m k` the
  `Ret` of `m` is where `k` begins, so a window `m` abandons ESCAPES into
  `k` (counterexample: `m` a bare exclusive read that returns, `k` a plain
  store).  The honest bind lemma would need `k` walkable under an arbitrary
  window, i.e. essentially `gquiet` — true at the abandoning sites, false
  for ordinary continuations.  `gwalk`'s window mode therefore keeps the
  CLOSED reading, which is now strictly stronger than `amo_tail` (as its
  `ExtraOutcome` arm already was), so `gwalk_amo_tail`/`gwalk_shaped` stay
  sound; the two C1 refutations (`gwalk_some_quiet_False`,
  `amo_tail_quiet_False`) are now FALSE and are replaced by the positive
  `gquiet_amo_tail` (quiet code abandons a window).  **C3 must add one
  index — "no window escapes `m`" — under which the bind lemma splits into
  the escape-free case (the present one, for the ~330 functions issuing no
  exclusive read) and the escaping case (quiet continuation).**  It is a
  sweep-side addition; the SPECIFICATION is settled in `WeakSailLTS`.
- **C3 (LANDED 2026-08-13, PARTIAL — the two premises STAY)** — the
  generator, the kit completion and the sweep landed; the two `∀ b`
  premises could NOT be deleted, because BOTH stage-C goals are still
  false/blocked for two reasons neither C1 nor C2 looked at.  See the
  findings (O4)/(O5) below.  What landed:
  - **`tools/gen_shape.py`** (+ `make gen-shape` / `make check-shape`), in
    the `gen_code.py` style: parses `model-xv6iris/rv64d.v`, builds the
    call graph (identifier closure with comments, string literals AND
    LOCALLY-BOUND NAMES removed — without the last filter the graph has
    spurious cycles, because Sail names local `let`s after global
    definitions), topologically sorts the monadic definitions reachable
    from `try_step` and emits `iris/WeakShapeGen<nn>.v` shards:
    `Lemma gw_<f> : ∀ a0..an, gwalk None (@<f> a0..an).
     Proof. intros; cbv [<f>]; gw_solve. Qed.` + `Hint Resolve … : gshape`.
    Arity comes from the binder region (the text up to the depth-0 `:`);
    `@` is used so implicit/typeclass binders are quantified positionally
    and nothing is left as an evar; a PATTERN binder (`'(C x)`) is
    destructed up front, because with two of them the body is a `match`
    APPLIED to the remaining arguments and no tactic rule sees that.
    Shard *n* Requires **every** earlier shard — `#[export]` hints are
    activated by `Import` and are NOT re-exported transitively, so
    requiring only *n−1* silently loses shard 1's hints at shard 3 and the
    symptom is an "incomplete proof" in a lemma whose callee was proved two
    shards back (lifted to `durable-notes.md`).  The generator is
    idempotent on disk (it rewrites a shard only when its text changes),
    and `iris/WeakShapeTop.v` sits on top of the tower.
  - **`iris/WeakShapeOverrides.v`** — the hand-written half: the
    `gwalk`-mode combinators `WeakShape` only had in `gok`/`gquiet` mode;
    **`gsilent`** (quiet UP TO FAILURE — `gquiet` refutes a `GenericFail`,
    which ~100 of the model's functions contain, so it cannot be the
    sweep's predicate); **the ESCAPE INDEX C2 asked for** (`gwalkx`, the
    weak/abandonment-permitting window reading, with `gwalk_gwalkx`,
    `gwalkx_shaped`/`gwalkx_amo_tail` and the two bind lemmas:
    `gwalkx_bind` for escape-free `m`, `gwalkx_bind_silent` for the
    escaping case with a `gsilent` continuation — added as a NEW fixpoint
    rather than by editing `gwalk`, so every closed-reading lemma of
    `WeakShape` transfers unchanged); the tactics `gw_solve`/`gsl_solve`;
    and §5, the two refutations.
  - **the sweep itself**: 294 of the 341 monadic definitions reachable
    from `try_step` are GENERATABLE as `gwalk None` (= `sail_shaped`
    generalised to any monad type); the 47-function residue is exactly the
    up-cone of `read_ram`/`write_ram` and of the three opaque monadic
    axioms, plus `_rec_pt_walk`.  **96 of the 294 are machine-checked in
    the tree** (`WeakShapeGen01..02.v`), the cut being `gen_shape.py`'s
    `--limit`.  THAT CUT IS A COMPILE-TIME BUDGET, NOT A DIFFICULTY
    BOUNDARY, and the budget is the thing to plan around next time:
    measured here, one 48-lemma shard costs **8–13 minutes of `coqc`**
    (the extension-enum dispatches dominate — `_rec_currentlyEnabled`
    alone is 140 s), the cost RISES up the topological order (shard 3 was
    still running at 33 min when it was cut), and **the shards cannot be
    built in parallel** because the hint database is the dependency
    mechanism and each shard `Require`s all the earlier ones.  The whole
    294 is a multi-hour serial chain; raise `--limit` and regenerate when
    there is a budget for it (`make gen-shape` lists exactly which
    functions are below the cut).
  - **the model's fuel recursions** are the only functions `cbv` +
    `gw_solve` cannot do alone; they are hand-proved in
    `gen_shape.py`'s `OVERRIDE_PROOFS` table (emitted at the group's
    topological position, so a regeneration cannot revert them):
    `_rec_hartSupports` by `fix` on its `Acc` argument, and the NINE-WAY
    mutual `_rec_check_stateen_bit`/`_rec_currentlyEnabled`/… block by one
    `fix` on the SHARED `Acc` proving all nine at once.  The shape that
    made the mutual one work: after `destruct acc as [acc]`, assert the
    nine PER-MEMBER instances `K1..K9` of the induction hypothesis at the
    accessibility subterms `acc y H` — `eauto` cannot project a
    conjunctive IH, and applying the IH to anything but a subterm breaks
    the guard condition.

## FINDINGS (2026-08-13, C3 — machine-checked): BOTH stage-C goals are
## STILL false, for the MIRROR of (O2) and for three opaque model axioms

- **(O4)** `∀ b, sail_shaped (riscv_step b)` is REFUTABLE — **a standalone
  store-conditional**.  `rv64d.execute_STORECON` issues
  `vmem_write … (con := true)` → `checked_mem_write … (con := true)` →
  `write_kind_of_flags aq rl true = Write_RISCV_conditional[_release]` →
  `write_ram Write_RISCV_conditional …`, i.e. a `MemWrite` whose access
  kind is `AV_exclusive` (`ak_latest = true`), **with no exclusive
  `MemRead` anywhere in the instruction**: the lr/sc reservation lives in
  the model's PURE axioms (`load_reservation`/`match_reservation`/
  `valid_reservation`), not in a memory event, and the matching `lr` is a
  DIFFERENT `riscv_step`.  `sail_shaped`'s window-closed `MemWrite` arm
  demands `ak_latest = false` off device addresses, so it is false at
  every `sc`.  Machine-checked at the site:
  `WeakShapeOverrides.gwalk_write_ram_con_False` /
  `sail_shaped_write_ram_con_False`.
  This is the EXACT MIRROR of C1's (O2), which found the READ side (an
  exclusive read with no conditional write) and fixed it in C2; the write
  side — a conditional write with no exclusive read — was never looked at.
  RECOMMENDED FIX (the symmetric one, and it is a stage-C2-scale spec
  change, not a sweep change): (i) drop the `ak_latest = false` conjunct
  from `sail_shaped`'s window-closed `MemWrite` arm; (ii) add a BARE
  CONDITIONAL-WRITE arm to `sail_mstep` — the write steps as a plain
  `LStore` (the machine only GAINS behaviors, the safe direction, exactly
  as C2's bare exclusive-read arm did); (iii) the ⇐ reconstruction gains a
  target-indexed run-local side condition ("no bare conditional writes in
  the block") joining `dev_ok_blk`/`fused_blk`, discharged per image by
  the checker (the xv6 kernel uses `amoswap`, not `sc`).  Ripple:
  `WeakSailLTS`, `WeakSailLTS2`, `WeakSailComplete` (`tail_complete`,
  `amo_reach`), `WeakSailCone`, `WeakComposeLang.wl_lift`.
- **(O5)** BOTH `∀ b` facts are additionally BLOCKED by **three opaque
  monadic axioms of the generated model**: `rv64d` declares
  `load_reservation`, `cancel_reservation` and `plat_term_write` as
  `Axiom`s of type `M unit`, and all three are reachable from `try_step`
  (`vmem_read_addr`, `execute_STORECON`, `htif_store`).  Nothing about an
  opaque constant's shape is provable OR refutable, so even with (O4)
  fixed the two facts cannot be closed outright.  RECOMMENDED NARROWING:
  replace the two `∀ b` premises by three POINT premises
  (`∀ …, gquiet (load_reservation …)` and the two others) — they are in
  the same ledger family as the 5 rv64d axioms `Print Assumptions`
  already reports, they are one line each, and they are the honest
  statement of what the model does not say.  (The alternative — giving the
  three axioms definitions in `model-xv6iris/riscv_extras.v` — moves the
  same assumption into the model.)
- **(O3), the liveness half, was NOT reached and is NOT refuted here.**
  Two C1 candidates were checked and are DEAD: `mem_read_priv_meta`'s
  `throw` arms need `(aq, rl) = (false, true)`, and every `vmem_read`/
  `mem_read` call site passes `rl := aq && rl`, so they are unreachable;
  and `checked_mem_read`'s `untilMT` has measure `N` with exactly `N`
  iterations, so its termination guard is provable from `N ≥ 1`.  The
  liveness half is therefore still OPEN, behind (O4)/(O5), and behind the
  ~100 remaining reachability obligations.

- **C4 (LANDED 2026-08-13)** — (O4)'s spec fix, machine-checked; (O5) is
  wired but the two `∀ b` premises STAY (the capstones are untouched).  What
  landed:
  - **(O4)** the window-CLOSED `MemWrite` arms of `sail_shaped`, `sail_mstep`
    and the kit's `gwalk`/`gwalkx` lost the `ak_latest = false` conjunct (the
    `n ≠ 0` one stays), so a STANDALONE conditional write is shaped and steps
    as a plain `LStore`.  **The arm is ONE STEP, not a bracket** — and that
    asymmetry with C2's bare exclusive READ is the point: C2 had to bracket
    because a one-step bare read leaves the hart in "window mode", where the
    residual is not `sail_shaped`; a standalone `sc` has no open window, so
    its residual `k (inl None)` is ordinary and
    `sail_shaped_res_step`/`tail_complete` go through untouched.
    `amo_tail`'s write arm is unchanged (inside a window a write must still
    BE the closing conditional write).
  - **`wrun`'s verdict on a standalone conditional write: it ACCEPTS it** —
    `WeakInterp.wrun`'s `MemWrite` arm never inspects `ak_latest` — **but a
    side condition is still needed, for the MESSAGE CLASS**: `wrun` computes
    `wm_class_of = WCexcl` there while a pf `LStore` step carries
    `lbl_class = WCrel/WCplain`, and the ⇐ reconstruction needs the two logs
    to agree syntactically.  (The alternative — making `lbl_class` read the
    source node instead of the label — was rejected: `WeakRetag.cls_canonical`
    takes `clsf : wlabel → wstate → wm_class` as a parameter, so a
    node-dependent class would ripple into the retag machinery.)
  - so the ⇐ cost went into the EXISTING predicate rather than a third one:
    `pf_solo_f` gains `¬ at_con_write i c` beside its
    `at_excl_read i c → pc_log c' ≠ pc_log c`, and **`fused_blk` now reads
    "every exclusive access of the block is part of a fused rmw"**.  Its
    shape, its target-indexing and every signature that carries it
    (`sail_run_wrun`/`sail_block_wrun`/`wprim_hart_block*`/`wl_lift`'s
    SegHart) are UNCHANGED — no new premise anywhere, and `WeakSailCone`/
    `WeakComposeLang` needed only prose.  A conditional-write configuration
    is reachable only for a STANDALONE write, because the fused arm consumes
    the write node inside its bracket.
  - suppliers of `pf_solo_f` pay almost nothing: `pf_solo_q_f` gets a second
    vacuity argument from the new `con_write_lbl` (a step from a
    conditional-write node emits an `LStore`, never a quiet label);
    `pf_rstep` derives `¬ at_con_write` from its own `LRmw`; `pf_sstep` now
    returns `pf_solo` plus `¬ at_con_write i c → pf_solo_f …`, and
    `tail_step`'s RAM-write arm splits on `ak_latest`, reporting a standalone
    conditional write through the SAME `fu : bool` flag C2 introduced for the
    bare read.
  - `WeakShapeOverrides` §5's two refutations
    (`gwalk_write_ram_con_False`/`sail_shaped_write_ram_con_False`) are FALSE
    now and are deleted, replaced by the positive leaves
    `WeakShape.gwalk_write_ram_con` and
    `WeakShapeOverrides.gwalkx_write_ram_con` (both with the `0 < width` side
    condition `gwalk_write_ram_plain` already carried).
  - **(O5) is wired, not discharged.**  `WeakShapeTop`'s `rv64d_axiom_shapes`
    record keeps its three `gquiet` facts and now also exports the `gsilent`
    forms (the window-crossing shape `execute_STORECON`'s tail needs).  §4
    adds `riscv_step_shaped_cone` / `riscv_step_ok_cone`: the `∀ b` premises
    reduce to `gwalk None`/`gok` of exactly TWO model functions,
    `try_step n b` and `tick_clock tt`.
  - **`riscv_step_shaped_ax` was NOT reached, and the blocker is (a), not the
    proofs.**  Every function between `try_step` and the memory cone calls
    into the part of the sweep that is BELOW the `--limit` cut (`try_step`
    alone needs `should_inc_minstret`, `run_hart_waiting`, `handle_interrupt`,
    `handle_exception`, `exception_handler`, `set_next_pc`), so no bridge
    lemma above the memory cone can even be stated before the remaining ~198
    generated lemmas exist — and that is a SERIAL multi-hour `coqc` chain
    (the shards `Require` each other; ~10 min for shard 2, C3 measured shard 3
    still running at 33 min).  Generating one more shard would have raised
    coverage without unlocking anything, so C4 spent its budget on the spec
    fix instead.  The liveness half was not attempted for the same reason.
    MEASURED ON THIS BOX (32 cores, `-j12`): shard 01 ~7 min, shard 02 ~7 min
    (serial -- the `Require` chain), and the whole affected chain
    `WeakSailLTS -> LTS2 -> Complete -> Shape -> Overrides -> Gen01 -> Gen02
    -> Top` plus `Cone -> Compose -> ComposeLang` rebuilds in ~15 min, of
    which 14 are the two shards.  The C3 figure ("~10 min/shard, rising")
    holds: budget the C5 chain at >= 4 more shards, rising, with NO
    parallelism available.

- **C5 (LANDED 2026-08-13/14, PARTIAL — the two premises STILL STAY)** — the
  generated tower is COMPLETE (all 294 lemmas, 15 shards) and the shape
  premise is now reduced, machine-checked, to TWELVE named model functions;
  but the residue could not be closed, because C5 found the obligation is
  bigger than C4 recorded and is blocked on a second generator-scale item
  ((O6) below).  What landed:
  - **the tower, to 294** (`gen_shape.py --limit` now defaults to 0 = the
    whole sweep): `WeakShapeGen01..15.v`.
  - **TWO TACTIC-PERFORMANCE FIXES that decide whether the sweep is feasible
    at all** — finding (O8).  Before them the chain was heading for >4 hours
    with individual shards apparently hung; after them **the whole tower
    plus `WeakShapePeel` and `WeakShapeTop` builds in 5 min 20 s serially**
    (Gen01 68 s, Gen02 70 s, Gen03..15 ~2 min total, Peel 52 s).  Both are in
    `WeakShapeOverrides.v` §4 with the measurements at the site.
  - **`iris/WeakShapeOverrides2.v` — `gpost`, the VALUE side of the kit.**
    Every predicate the sweep had (`gwalk`/`gwalkx`/`gsilent`) is blind to
    `Interface.Ret`'s payload, and two of the residue's three semantic
    obligations are facts about a RETURNED VALUE.  `gpost Q P m` = "no memory
    event, no barrier; every returned value satisfies `P`; every raised Sail
    exception satisfies `Q`", i.e. `gsilent` with the `Ret` arm strengthened
    and the `ExtraOutcome` arm weakened.  **Its `ExtraOutcome` arm must IGNORE
    the continuation** — `throw e` is `Next (ExtraOutcome e) mret` and `bind`
    pushes the rest of the computation into that continuation, so an arm that
    recursed would demand `∀ r, P r` at every `throw`; ignoring it is also
    exactly what the only consumer (`try_catch`, hence `liftR` and
    `catch_early_return`) does.  Combinators: `gpost_bind`, `gpost_try_catch`
    (the one that turns the exception postcondition into part of the value
    postcondition), `gpost_liftR`, `gpost_catch_early_return`, and the three
    CONSUMERS `gwalk_bind_post`/`gwalkx_bind_post`/`gsilent_bind_post` that
    carry a value fact into a shape obligation.
  - **the first semantic obligation, DISCHARGED**: `gpost_split_misaligned`
    (`0 < width → 0 < split_width`), over `gpost_split_access` +
    `count_trailing_zeros_nonneg` + a generic `foreach_Z_down'_inv` — and the
    write leaf it feeds, GENERALISED over the access kind
    (`gwalk_write_ram_any`/`_solo`).  Since C4's (O4) fix the window-closed
    `MemWrite` arm constrains only the width, so `WeakShape` §6b's
    kind-specific leaves collapse into one lemma good for EVERY `write_kind`
    (the three "unused" kinds are `internal_error` nodes the walk crosses).
    That generality is not cosmetic: in `checked_mem_write` the kind is a
    BOUND VARIABLE (`write_kind_of_flags aq rl con`'s result), never a
    literal.
  - **the second, DISCHARGED modulo its callees**: `gw__rec_pt_walk` /
    `gw_pt_walk`, by the same `fix`-on-the-`Acc`-argument recipe as
    `_rec_hartSupports`, stated over hypotheses for its three monadic callees
    (`read_pte`, `pte_is_invalid`, `check_leaf_pte`).
  - **`iris/WeakShapePeel.v` — the frontier, machine-checked.**  With the
    tower complete, `try_step`, `run_hart_active` and `execute` are ordinary
    `cbv` + `gw_solve` modulo their residue callees, so
    `WeakShapeTop.riscv_step_shaped_residue` reduces
    `∀ b, sail_shaped (riscv_step b)` to TWELVE one-line facts: `fetch` and
    the eleven memory `execute_*` clauses.  `tick_clock` is discharged
    outright, as are `htif_store` and `mmio_write` (`WeakShapeTop`, off the
    axiom record — the HTIF path's only obstacle was `plat_term_write`).
  - **THREE COVERAGE HOLES in `gen_shape.py`, all found by trying to use the
    tower, two fixed:**
    (i) `is_monadic` tested the definition head for `' M ('`, and Sail wraps a
    long signature so that `: M (...)` starts a line — `check_leaf_pte` was
    therefore in NEITHER the generated set NOR the reported residue.  The test
    now normalises whitespace; `check_leaf_pte` is in `SKIP` (hand-proved
    beside `_rec_pt_walk`) so the built shards stay byte-identical.  The same
    hole had hidden `translate`/`translate_TLB_hit`/`translate_TLB_miss`, so
    **the residue is 51 functions, not 47.**
    (ii) the call graph is rooted at `try_step` ALONE, but
    `RiscvLang.riscv_step` also calls `tick_clock`, whose cone adds two
    monadic definitions no shard covers.  Proved by hand in `WeakShapePeel`;
    rooting the generator at both would renumber and rebuild every shard.
    (iii) THE TOWER HAS ONE MODE.  Every shard proves `gwalk None`, which does
    NOT imply `gsilent`/`gpost` (it permits memory events) and says nothing
    about liveness.  So the postcondition sweep (O6) and the liveness half
    (O3) each need their OWN generated lemmas over the same cone.  With (O8)
    fixed that is now a ~5-minute chain per mode rather than a multi-hour one,
    which changes the calculus completely — but it is still a REGENERATION,
    so decide the mode set before generating.
  - **`gen_shape.py` also gained `--shard-sizes`** (comma list, last value
    repeats; default `48,48,16`) and now DELETES stale higher-numbered shards,
    which a re-shard would otherwise leave on disk where `make check-shape`
    cannot tell them from hand-written files.  Finer shards high up the order
    are how partial progress survives a killed build — there is no partial
    `.vo`, and that is what turned one 60-minute loss into a 90-second one
    while (O8) was still undiagnosed.

## FINDINGS (2026-08-13/14, C5 — machine-checked): the width obligation does
## not stop at the memory cone, and the sweep's cost was a TACTIC bug

- **(O6)** `∀ ast, gwalk None (rv64d.execute ast)` is **REFUTABLE**, and it is
  the only form of `execute`'s lemma a compositional route can use.  Sail's
  `(0 <? width) && (width <=? 4096)` precondition is emitted as a COMMENT;
  `word_width` is `Definition word_width : Type := Z`, so `STORE (imm, rs2,
  rs1, 0)` is a well-typed `instruction`, and on it the model issues a
  ZERO-WIDTH `MemWrite` (`split_misaligned` returns `(1, width)` on its
  unsplit path), which `sail_shaped`/`gwalk`/`gwalkx`/`sail_mstep`'s `LStore`
  arm all refuse.  Machine-checked at the leaf:
  `WeakShapeOverrides2.gwalk_write_ram_zero_False`.
  The `∀ ast` is unavoidable: `run_hart_active` applies `execute` to
  `ext_decode w`'s output AND, in the `ExecuteAs other_inst` arm, to an
  `instruction` VALUE the first `execute` returned — neither is syntax.
  **`sail_shaped (riscv_step b)` itself is NOT refuted** (the widths the
  decoder builds are `word_width`-derived, hence in `[1;2;4;8]`); what is
  refuted is the ROUTE.  Closing it needs a DECODER POSTCONDITION — `gpost` of
  `encdec_backwards` with `P` = "every width field of the resulting
  `instruction` is in `[1;2;4;8]`", plus the same postcondition on `execute`'s
  own `ExecuteAs` values.  MEASURED: `gw_encdec_backwards` (the ~4000-line,
  ~250-arm decoder) costs 312 s standalone in the `gwalk` mode, so the
  decoder is not itself a wall — the missing piece is the `gpost` mode.
  The residue's THIRD semantic obligation (the exclusive window) is the same
  shape: it needs `gpost` of `pmaCheck`
  (`LoadReserved`/`StoreConditional`/`Atomic` answer `CannotSplit`, because
  their `is_mag_applicable_access` is `false` and their
  `pma_misaligned_exception` is an `internal_error`/`Some`, so a misaligned
  exclusive access faults before any `read_ram`), hence `N = 1` and the window
  is opened at most once.
- **(O7)** A GENERATED SWEEP SHOULD EMIT EVERY MODE IT WILL EVER NEED IN ONE
  PASS.  The shards form a serial `Require` chain, so a second mode is the
  whole chain again; `gwalk None` implies neither `gpost` nor `glive`.
- **(O8), THE EXPENSIVE FINDING, and the one that generalises: THE SWEEP'S
  COST WAS A TACTIC BUG, NOT THE MODEL.**  C3/C4 measured "7-10 min per
  48-lemma shard, rising up the order" and C5 watched a shard run 60 minutes
  without finishing.  Both were artefacts of `gw_leaf`, and there were two
  independent causes, each worth ~an order of magnitude:
  1. **A LEAF TACTIC RUNS AT EVERY NODE, NOT ONLY AT LEAVES.**  `gw_solve`
     tries `solve [gw_leaf]` before every structural step, so at a `bind` —
     where no leaf can succeed — every alternative still ran on the whole
     subterm.  `apply gwalk_quiet` / `apply gsilent_gwalk` succeed on ANY
     `gwalk None ?m` goal and then hand it to `eauto`.  Gate the leaf on the
     goal being ATOMIC (`gw_atomic`, a `lazymatch` that fails on every
     combinator head).
  2. **A `discriminated` HINT DB PRUNES BY HEAD CONSTANT ONLY IF THE CONSTANTS
     ARE OPAQUE TO IT.**  Every hint concludes `gwalk None (<model function>
     ?a …)` and the generated model's definitions are TRANSPARENT, so `eauto`
     delta-unfolded them while matching and compared BODIES — and sibling
     functions in a band share a long prefix, so each failed match descended
     through two huge terms, once per hint, per node.  One line fixes it:
     `Hint Constants Opaque : gshape`.
  Measured: `rv64d.legalize_mie` **>40 min → 0.9 s**; `rv64d.write_CSR`
  **>18 min → 23 s**; `WeakShapeGen01` **7 min → 68 s**; the whole 294-lemma
  tower **>4 h (projected) → 5 min 20 s**.  THE DIAGNOSTIC THAT FOUND IT:
  compile a COPY of the stuck shard with `coqc -time` concurrently — the log
  streams, so the last line names the stalling lemma — then bisect the leaf
  tactic by deleting alternatives.  A "hung" generated shard is a tactic
  bug until proven otherwise.
- **the memory cone's own solver does NOT scale, and that is C6's first
  concrete task.**  `gw_htif_store` and `gw_mmio_write` go through in
  under a second, but `checked_mem_write` — even with `0 < split_width`
  supplied by `gwalk_bind_post` and the write leaf by `gwalk_write_ram_any` —
  explodes at ONE step of the generic solver, inside the misaligned-split
  `untilMT` body (25 steps of `gw_solve` are instant, 26 does not finish in
  200 s).  It needs a HAND-STRUCTURED script, not `gw_solve`: peel
  `catch_early_return`, the `check_pma` bind and the loop explicitly, and run
  the solver only on the loop body's leaves.

## What C6 owes (the list is shorter, and one item is bigger)

1. **THE DECODER POSTCONDITION** — `gpost` of `encdec_backwards` (and of
   `execute`, for its `ExecuteAs` values) with "every width field of the
   resulting `instruction` is in `[1;2;4;8]`".  Without it (O6) stands and
   `execute`'s `∀ ast` lemma is false, so nothing above the memory cone can be
   closed.  ~4000 lines, ~250 arms: a generator-scale item, and it must be
   emitted in the SAME pass as anything else that is generated (O7).
2. **The 51-function residue**, in the three modes it actually needs:
   `gwalk None` for the shape, `gpost` for the two value obligations
   (`0 < split_width` — DONE in `WeakShapeOverrides2` §2 given `0 < width`;
   `pmaCheck` answering `CannotSplit`, so the exclusive window opens once),
   and `gsilent`/`gwalkx` for the abandoning exclusive tails.  `_rec_pt_walk`
   and `pt_walk` are DONE modulo their callees.
3. **The three axiom facts**, consumed inside 2 at `vmem_read_addr`,
   `execute_STORECON` and `htif_store` via `WeakShapeTop`'s
   `gw_*`/`gsilent_*` lemmas — after which the capstones can take
   `rv64d_axiom_shapes` in place of the two `∀ b` premises.
4. **Liveness (O3)** — behind a whole SECOND generated tower in the `gok`
   mode (O7), then the ~100 `exit`/`internal_error`/`assert_exp` reachability
   sites, then the misaligned-split loop's termination.  It is the largest
   remaining item and it is strictly behind 1 and 2.  Since (O8) the tower
   itself is CHEAP (~5 min per mode), so the cost here is the ~100
   reachability arguments, not the sweep.

- **C6 (LANDED 2026-08-14, PARTIAL — the two premises STILL STAY)** — C5's
  item 1 (THE DECODER POSTCONDITION) is DONE, machine-checked and
  state-generic; and getting there turned up (O9), which is why it could not
  have been done before: **`∀ b, sail_shaped (riscv_step b)` was FALSE AS
  STATED, not merely unreachable by the compositional route.**  What landed:
  - **(O9), the finding, and its spec fix** — see below.  `WeakSailLTS`
    delta (e'''): `sail_shaped`'s and `amo_tail`'s `Interface.ExtraOutcome`
    arm is `True`.  `WeakShape.gwalk` follows in the window-CLOSED mode only
    (the window-open `False` is a kit-side strengthening `gwalk_try_catch`
    needs — see the arm's comment); `WeakShapeOverrides.gwalkx` follows in
    both.  Fallout was five proof lines in `WeakShape`/`WeakShapeOverrides`
    and one tactic branch in `WeakShapeOverrides2.gwalk_write_ram_any/_solo`
    (the three "unused" write kinds are `internal_error` nodes, i.e.
    `ExtraOutcome`s, and they are now admitted outright instead of by
    `intros r`); **everything from `WeakSailLTS2` down — `WeakSailComplete`,
    `WeakSailCone`, `WeakCompose`, `WeakComposeLang` — needed NOTHING**,
    because the LTS is stuck at such a node and every completeness proof
    already went to `exfalso` through `block_forced_stuck` there.
  - **`iris/WeakShapeAst.v`** — `ast_wf`, the postcondition, EXACTLY as
    strong as the residue needs (`0 < width` on the six width-carrying
    constructors, `True` elsewhere; NOT the `[1;2;4;8]` membership
    `DecodeSetU.width_ok1248` records, which no consumer wants); §1's
    machine-checked leaf for (O9) (`throw_bind_node`,
    `liftR_throw_bind_node`); §3's consumers (`gwalk_bind_pure`,
    `gwalkx_bind_pure`, `gpureP_liftR`, `gpureP_spine`,
    `gpureP_spine_pure`); and §4 **`gpure`**, the mode.
  - **`gpure` = `gpost (λ _, True) (λ _, True)`** — `gsilent` with the THROW
    arm opened up.  It is forced: three functions of the decoder's own cone
    (`zicfiss_xSSE`, `_rec_get_xLPE`, `_rec_virtual_memory_supported`) raise
    `internal_error`, so `gsilent` refutes them, and `gwalk None` (what the
    tower proves) does not imply any value-carrying mode.  Full combinator
    kit + `gpu_solve`, same (O8) discipline (gated atomic leaf,
    `Hint Constants Opaque`).
  - **`iris/WeakShapeDec.v`** — the decoder's whole cone (35 monadic
    definitions, incl. the nine-way mutual `stateen` fuel block and
    `_rec_hartSupports`, by the `fix`-on-the-`Acc` recipe) in `gpure`, and
    then the two theorems:
    **`gpureP_ext_decode : ∀ w, gpureP ast_wf (ext_decode w)`** and
    **`gpureP_ext_decode_compressed`**.  MEASURED: the cone 19 s, the whole
    file (cone + both ~250-arm traversals) **54 s**.
  - **WHAT WAS REUSED FROM `iris/DecodeSetU.v`, AND WHAT COULD NOT BE.**
    `DecodeSetU` already walks both decoders with a leaf predicate
    (`goodbP D P m s`) and gets the COMPLETE decode image
    (`decodable_u`/`decodable_c`, hence `width_ok1248` on every memory
    clause).  It is VALUE-PINNED at the U-mode reference state `dstateU` —
    its `RegRead` arm answers from a concrete register file, which is what
    lets `dtp_pin` `vm_compute` disabled extension families out of the image.
    The fetch in `run_hart_active` runs at an ARBITRARY register state, so
    what was reused is the METHOD, not the theorems: the clause-spine rule
    (`goodbP_spine` ⇝ `gpureP_spine`), the driver's shape (`dtp_core` ⇝
    `dp_core`), the `width_enc_wide_backwards` Q-rule (`dtp_width_wide` ⇝
    `dp_width_wide`), and the observation that **the width fields are
    gate-INDEPENDENT** (they come from `width_enc_backwards` /
    `width_enc_wide_backwards` on a funct3/funct2 slice), so dropping the
    pinning costs dead arms and never a width.  THE GENERAL RULE: a
    state-pinned boolean traversal and a ∀-quantified `gpost` traversal are
    the SAME traversal with different `RegRead` arms; port the driver, not
    the theorem, and drop exactly the pinning arm.
  - **`sail_shaped`'s premise is NOT yet reduced further.**  The peel
    (`WeakShapePeel`) and `WeakShapeTop.riscv_step_shaped_residue` are
    UNCHANGED: consuming the decoder postcondition at `run_hart_active` needs
    one more piece, and C6 stopped there — see "what C7 owes" (1).

## FINDING (2026-08-14, C6 — the leaf machine-checked, the path from the
## sources): (O9) — `∀ b, sail_shaped (riscv_step b)` was FALSE AS STATED

- **(O9)** `Interface.ExtraOutcome {A} : eOutcome A -> outcome A` is indexed
  by **the monad's own return type**, and `Defs.throw e = Next (ExtraOutcome
  e) mret`, so `Defs.bind (Defs.throw e) k = Next (ExtraOutcome e) k`
  (`WeakShapeAst.throw_bind_node`).  Through C5 `sail_shaped`/`gwalk`/`glive`
  handled the node by their DEFAULT arm, `∀ r, sail_shaped (k r)` — i.e. they
  walked the ENTIRE REST OF THE INSTRUCTION at every value of the thrown-at
  type.  `WeakSailComplete`'s header (a) already justified that arm with
  "their result types are empty (or abstract)", which is true of
  `GenericFail`/`Discard` (result type `False`) and FALSE of `ExtraOutcome`.
  **THE PATH THAT MAKES IT BITE:** `run_hart_active` binds
  `liftR (ext_decode w) >>= λ instruction, … execute instruction …`;
  `encdec_backwards`'s SSPUSH arm evaluates
  `and_boolM (currentlyEnabled Ext_Zicfiss) (read_reg cur_privilege >>=
  zicfiss_xSSE)`; `currentlyEnabled Ext_Zicfiss` bottoms out in
  `currentlyEnabled Ext_A = misa.A`, a REGISTER, so the gate is true at
  ordinary states; and `zicfiss_xSSE VirtualSupervisor = internal_error
  "Hypervisor extension not supported" = throw …`.  Every shape predicate's
  `RegRead` arm quantifies over `cur_privilege`'s answer, so the old arm
  demanded `sail_shaped` of the continuation at EVERY `instruction` —
  exactly the `∀ ast` that C5's (O6) refutes at `STORE (imm, rs2, rs1, 0)`.
  (`_rec_get_xLPE` throws the same way behind the same gate;
  `amo_encoding_valid`'s `reserved_behavior` arm is dead only because
  `amocas_odd_register_reserved_behavior = AMOCAS_Illegal` here.)
  **FIX (LANDED): (O1)'s fix applied to a third arm** — quantify over the
  answers `sail_mstep` SUPPLIES, and it supplies NONE for `ExtraOutcome`
  (the agent is stuck; `WeakSailLTS2`'s unbracket cases say so).  Arm := `True`.
  **THE GENERALISABLE RULE, and it is the sixth instance of this genre:**
  for EVERY outcome constructor, check (a) whether the LTS has an arm for it
  and (b) **what its ANSWER TYPE is** — a predicate arm `∀ r, P (k r)` over
  an answer the machine never supplies is a silent, unbounded strengthening,
  and the danger is highest exactly where the answer type is not `False` but
  is not observed either.
- **the liveness half is refuted by the SAME witness, and not by a shape
  bug.**  `glive`'s `ExtraOutcome` arm is `if xf then False else True`, so
  `sail_live` FORBIDS a raised exception outright and the `zicfiss_xSSE` path
  is reachable in the same ∀-quantified sense.  What that needs is the (O3)
  reachability narrowing — xv6 runs with the H extension off, so
  `cur_privilege` is never `VirtualSupervisor`/`VirtualUser` — i.e. **a
  register-state side condition, which is why the liveness half cannot be
  stated as `∀ b` at all.**  Recorded, not fixed: the honest shape is
  `sail_live` under a register-state precondition (the `D-M6-8` checker
  family), and it should be settled BEFORE a `gok` tower is generated.

- **C7 (LANDED 2026-08-14, PARTIAL — the two premises STILL STAY, and now we
  know the FIRST one is FALSE)** — C6's item 1 is DONE (the decoder
  postcondition is CONSUMED at `run_hart_active`), the `gwpx` mode and the
  value sweep exist, and the residue is restated well-formed; but the memory
  cone was NOT attempted, because C7 found **(O10)**: `∀ b, sail_shaped
  (riscv_step b)` is REFUTABLE AGAIN, at `update_and_write_pte`, and every one
  of the twelve residual facts is false as a consequence.  What landed:
  - **`iris/WeakShapeWin.v` — `gwpx Q P w m`, the VALUE-AND-WINDOW mode.**
    C6 asked for "`gwalk` with a Ret postcondition"; the consumers forced one
    more index, and it is the design point: **`P : A → win → Prop` takes the
    WINDOW THAT IS OPEN AT THE RETURN.**  With it ONE fixpoint is the whole
    kit — `gwalk w m` is EXACTLY `gwpx (λ _, True) (λ _ w', w' = None) w m`
    (both directions proven: `gwalk_gwpx`/`gwpx_gwalk`), `gwalkx` is the
    `λ _ _, True` instance up to the throw arm (`gwpx_gwalkx`), and
    `run_hart_active` needs NEITHER: what it needs is "if `execute` returns an
    `ExecuteAs` redirection then the payload is `ast_wf` AND no window is
    open" (`exres_wf_win`), so the redirection arm may call `execute` again
    while `execute_LOADRES` still abandons.  A value-only `P` cannot state
    that and the `gwalkx`/`gsilent` split cannot either (the redirection arm
    is not silent).  The `ExtraOutcome` arm keeps `gwalk`'s KIT-SIDE
    strengthening (`False` under an open window) — that is what lets
    `gwpx_try_catch` hand the handler over at a closed window, which `liftR`
    and `catch_early_return` both need.
    ONE BIND RULE (`gwpx_bind`) specialises to every other: `gwpx_bind_closed`
    (prefix from the `gshape` tower), `gwpx_bind_pure` (prefix from
    `gpureP`, i.e. the decoder), `gwpx_bind_exres` (prefix whose
    `ExecutionResult` the continuation matches on), plus the consumers
    `gwalk_bind_wpx`/`gwalkx_bind_wpx`.  Solver `gwx_solve` under the (O8)
    discipline (gated atomic leaf, `Hint Constants Opaque` on `gwpost`/
    `gwexec`).
  - **`tools/gen_shape.py --mode exec` + `iris/WeakShapeExecGen01..03.v`** —
    116 lemmas: `gwx` (= `gwpx` at `exres_ok` = "`exres_wf` and no window
    open") for the 61 `ExecutionResult`-returning monadic definitions outside
    the memory cone, and `exres_wf` for the 55 PURE `ExecutionResult`
    producers (the compressed expansions, whose `ExecuteAs` payloads carry
    literal widths).  `make gen-shape` now emits BOTH modes (finding (O7)),
    `make check-shape` checks both.
    **MEASURED: the whole second mode is 9 s of `coqc`** (5.2 + 3.0 + 1.2),
    against 5 min 20 s for the `gwalk` tower — because `gwpx`'s bind rule
    takes `gwalk None` for the PREFIX, so the 294-lemma tower is reused
    verbatim and only the ~60 clause BODIES are walked.  THE GENERAL RULE:
    a second mode over the same cone is cheap exactly when its bind rule can
    consume the first mode at the prefix; design the modes so that it can.
  - **`iris/WeakShapeExec.v`** — `gx_execute`/`gx_execute_closed` (both
    readings, modulo the eleven memory clauses now stated WITH `0 < width`)
    and `gwx_run_hart_active`/`gw_run_hart_active_wf`, where the decoder
    postcondition CROSSES into `execute`'s obligation and the `ExecuteAs`
    REDIRECTION is discharged.  `WeakShapeTop.riscv_step_shaped_residue_wf`
    is the restated residue; `WeakShapePeel`'s is left in place as the
    stage-C5 form.
  - **THREE TACTIC TRAPS, all of the (O8) family, all costing >30 min each:**
    (i) `try (by apply H1); try (by apply H2); …` over `execute`'s ~130 arms
    did not finish in two minutes — the model's `execute_*` are TRANSPARENT so
    every failing `apply` delta-unfolds two large terms.  Dispatch by HEAD
    CONSTANT with a `lazymatch`: 3 s.  **The (O8) lesson is not about hint
    databases, it is about `apply` against a transparent generated model
    anywhere.**
    (ii) **`∀ e, Q e` where `Q` is the SUM postcondition a
    `catch_early_return` installs does NOT reduce until the sum is
    destructed**, so `by intros` fails and every rule carrying that premise
    silently FALLS THROUGH to the next alternative.  Here the decoder rule
    fell through to the generic `gwalk` route, which walks the decoder happily
    and DROPS its postcondition — the symptom was `gwx (execute ?ast)` with no
    `ast_wf` in scope, four steps away from the cause.  `qtriv` (destruct the
    sum, then `exact I`/`reflexivity`) is the fix.
    (iii) a cleanup rule that `clear`s a postcondition hypothesis "not yet
    needed" fired BEFORE the value was destructed and threw away the very fact
    the redirection arm needed.  Unpack a postcondition only once its subject
    is a CONSTRUCTOR.
  - the capstones are UNTOUCHED and `Print Assumptions` on both is still
    EXACTLY the five rv64d axioms; `WeakCompose` §6 (6) and `WeakComposeLang`
    §D record (O9), (O10) and the liveness half's state-conditioned form.

## FINDING (2026-08-14, C7 — leaves machine-checked, path from the sources):
## (O10) — `∀ b, sail_shaped (riscv_step b)` IS FALSE AGAIN  [FIXED IN C8]

- **(O10)** `rv64d.update_and_write_pte` — on the path of EVERY memory
  instruction and of the FETCH, since every one of them translates — issues
  an **exclusive** PTE read (`read_pte_exclusive` = `mem_read_priv … (res :=
  true)`, and `read_kind_of_flags false false true = Read_RISCV_reserved`,
  which `WeakInterp.classify` maps to `AV_exclusive`), and then, on the arm
  where the **re-read** entry needs no update (`update_PTE_Bits pte' access =
  None`, and `pte'` is the ∀-quantified value of that read), returns
  `Ok (Some pte', ext_ptw)` — a SUCCESSFUL A/D update **with no conditional
  write**.  `translate_TLB_hit`/`_miss` treat that as success, `translate`
  returns `Ok`, and the instruction then performs its OWN data access — a
  `MemRead` inside the still-open window, which `amo_tail`'s arm refuses
  (`MemRead ↦ False`), or a `MemWrite` at the wrong address.  Machine-checked
  leaves in `WeakShapeWin` §1: `amo_tail_read_ram_False`,
  `gwalkx_read_ram_in_window_False`, `gwalk_excl_read_then_read_False` (the
  composite), `read_kind_of_flags_res`.  The enclosing gate is satisfiable at
  ordinary register states (`hartSupports Ext_Svadu = true` in this
  configuration and `menvcfg.ADUE` is a REGISTER).
- **IT IS THE SAME GENRE AS (O2)/(O4), NOT A NEW ONE — and it is where C2's
  fix ran out.**  C2 legalised an abandoned window by BRACKETING it in
  `sail_mstep` (`silent_run … (Interface.Ret y, rs1)`), i.e. by assuming the
  abandoned tail is SILENT.  Here the abandoned tail is *the rest of the
  instruction*, memory accesses included, so the bracket does not apply, the
  LTS is stuck, and the shape predicate is false.  **THE GENERALISABLE RULE:
  a "the tail is quiet from here" bracket is only as good as the CALL DEPTH
  at which the window is abandoned — an abandonment deep in a callee
  (`translate`) has the whole caller after it.**
- **THE FIX (specified, not implemented; it is a stage-C2/C4-scale change):**
  (i) `sail_shaped`'s `MemRead` arm DROPS the window entirely — an exclusive
  read is shaped exactly like a plain one — so `amo_tail` survives only as the
  hypothesis of `sail_mstep`'s FUSED rmw arm and of `amo_reach`, not as a
  claim `sail_shaped` makes; (ii) `sail_mstep`'s BARE exclusive-read arm
  becomes ONE STEP instead of a bracket, exactly as C4's standalone
  conditional write already is — C2 rejected the one-step form only because
  "it leaves the hart in window mode where `sail_shaped` is not preserved",
  and with (i) there is no window mode, so `sail_shaped_res_step` and
  `tail_complete` go through unchanged; (iii) the ⇐ cost goes where (O2)'s and
  (O4)'s went, into `pf_solo_f`/`fused_blk`, whose reading stays "every
  exclusive access of the block is part of a fused rmw" — per-image discharge:
  xv6 runs with `menvcfg.ADUE = 0`, so the A/D update path is never taken.
- **AND THE FIX COLLAPSES THE KIT, WHICH IS WHY IT SHOULD COME FIRST.** With
  (i) the window index leaves `gwalk`, `gwalkx` BECOMES `gwalk`, the
  "universal exclusive-window obligation" C6 recorded (every memory
  instruction pays it) EVAPORATES, and the memory cone loses its hardest
  semantic obligation — the read/write address-and-width agreement across
  `checked_mem_read`/`checked_mem_write`, which needed `pmaCheck`'s
  `CannotSplit` postcondition, `split_misaligned`'s `N = 1`, an `untilMT`
  unfolding at `N = 1`, and `add_vec_int … 0` reasoning.  `gwpx` survives
  unchanged (its `P`'s window argument becomes constantly `None`).
- **CONSEQUENCE C7 HAD TO STATE PLAINLY:** with (O10) open, the capstones'
  `(∀ b, sail_shaped (riscv_step b))` premise was UNSATISFIABLE, so
  `xv6_weak_robust_lifted`/`_adequate` were VACUOUS — the same genre as the
  ∀-path oracle premise (2026-08-13) and a fourth reason not to swap a premise
  for a record until the specification is right.  **C8 fixed the
  specification and then swapped it**; `∀ b, sail_live (riscv_step b)` is
  still refuted by (O9)'s witness and stays a premise, verbatim, for the
  reason recorded there.

- **C8 (LANDED 2026-08-14) — (O10)'s SPECIFICATION FIX, THE KIT COLLAPSE, THE
  MEMORY CONE, AND THE CAPSTONE SWAP.**  `∀ b, sail_shaped (riscv_step b)` is a
  THEOREM now — `WeakShapeTop.riscv_step_shaped_ax : rv64d_axiom_shapes → ∀ b,
  sail_shaped (riscv_step b)` — and `xv6_weak_robust_lifted`/`_adequate` take
  the three-fact record IN PLACE OF the premise.  Both capstones are still at
  EXACTLY the five rv64d axioms.  What landed:
  - **the fix, exactly as `WeakShapeWin` §1 specified.**  `sail_shaped`'s
    `MemRead` arm DROPS the window (an exclusive read is shaped exactly like a
    plain one) and **`amo_tail` is DELETED**, so `sail_shaped` is a plain
    non-mutual `Fixpoint` whose whole content is "no coherent read, no
    zero-width RAM write" — its two memory arms are now exact mirrors,
    `(if dev_addr … then True else <the one conjunct>) ∧ <recurse>`.
  - **the bare exclusive-read arm did not need to be added: it is the ORDINARY
    load arm.**  `sail_mstep`'s plain `LLoad` arm simply stopped requiring
    `ak_latest = false`, exactly as C4's `LStore` arm stopped requiring it on
    the write side.  THAT IS THE SHAPE OF ALL THREE FIXES ((O2)/(O4)/(O10)):
    each deleted a conjunct, and each time the "special" arm became the
    ordinary one — no new disjunct, no new mode, no new premise.
  - **the ⇒ bracket lost its mutual half.**  With no window there is no
    `amo_bracket`: `sail_bracket_all` is a plain structural induction and ⇒
    takes the one-step arm at every exclusive read (`wread_read_ok` drops the
    `ak_latest` pinning), i.e. an interpreter rmw maps to a load and a store
    rather than to a fused `LRmw`.  That only ENLARGES the pf behaviours the
    sail machine is shown to have — the safe direction — and the fused arm is
    what the ⇐ direction consumes.
  - **the ⇐ side kept the fused arm and re-based its evidence ON THE RUN.**
    `WeakSailLTS2.amo_unbracket` is now indexed by the `base : Z` the fused
    label carries and takes `sail_shaped m` where it took `amo_tail pa n m`:
    the address/width agreement between an rmw's read and its write is pinned
    by `sail_mstep`'s own fused arm (`base = pa_z (ReadReq.pa req)`,
    `length data = N.to_nat n`), so deleting the predicate's claim cost
    nothing.  `WeakSailComplete` §6's carriers became
    `sail_shaped_silent1`/`_silent_run` and a `sail_shaped`-hypothesis
    `wr_node_shaped`; `amo_step`/`amo_reach` are DELETED (at an exclusive read
    the completion now has exactly one arm).
    **THE GENERAL RULE: a multi-step protocol belongs in the RUN's evidence,
    not in a ∀-path predicate over the monad.**
  - **`pf_solo_f`/`fused_blk` ARE UNCHANGED, word for word** — "a step from an
    `at_excl_read` configuration APPENDS a message, and no step is taken from
    an `at_con_write` one".  It still excludes the bare arm (the fused arm is
    an `LRmw`, the bare one an `LLoad`) and it needs nothing about windows.
    `tail_complete` reports `fu := false` at an exclusive read exactly as it
    already did at a standalone conditional write; the `fu` machinery, its
    quiet-skeleton vacuity (`pf_solo_q_f`) and every signature carrying
    `fused_blk` are untouched.  Per-image discharge grows one clause: xv6 runs
    with `menvcfg.ADUE = 0`.
  - **THE KIT COLLAPSE, and it is why the rest was affordable.**  `gwalk` lost
    its `win` index (and `win` itself is gone); `gwalkx` is DELETED — it had
    become literally equal to `gwalk` — and with it the escape-index binds, the
    window-crossing binds, the window-mode raw nodes and leaves
    (`gwalk_MemRead_excl`, `gwalk_MemWrite_close`, `gwalk_write_ram_close`,
    `gwalk_bind_quiet`, `gquiet_amo_tail`, `gwalk_throw_some`,
    `gwalk_sail_barrier_some`, `gwalk_try_catch_live`, `gwalk_liftR_win`,
    `gwalk_catch_early_return_win`).  The three read-kind leaves collapse into
    one.  `gwpx Q P w m` becomes `gwp Q P m` with `P : A → Prop`;
    `exres_ok`/`exres_wf_win` collapse into `exres_wf`; `gx_execute_closed` and
    `gwx_run_hart_active` merge with their twins (ONE reading, not two).
    91 declarations deleted or renamed, ~1000 net lines gone.
  - **`iris/WeakShapeMem.v` — THE MEMORY CONE, 940 lines, 28 s of `coqc`.**  The
    whole 51-function residue, `read_ram`/`write_ram` up to `fetch`, plus the
    `rv64d_axiom_shapes` record (MOVED here from `WeakShapeTop`, because the
    cone consumes it) and `htif_store`/`mmio_write`.  Its ONLY side conditions
    are `0 < width` and the three axiom facts — the exclusive-window
    obligation C6/C7 had costed (`pmaCheck` ⇒ `CannotSplit` ⇒ `N = 1` ⇒ an
    `untilMT` unfolding ⇒ `add_vec_int … 0`) EVAPORATED with the index, which
    is why a stage-sized item finished inside C8.  Two width facts needed real
    work, both in `vmem_write_addr`: `0 < in_page_bytes` (from
    `uint_range`) and `0 < next_page_bytes` (by destructing `do_split_access`
    through a new `gwalk_bind_and_boolM`, rather than a `gpost` of
    `translationMode` the `gwalk` tower cannot supply — (O7) again).
  - **the eleven `execute_*` clauses, in the VALUE mode** (`WeakShapeExec` §3),
    over a value-mode companion for the cone's `ExecutionResult`-carrying
    functions (`gxr`, `WeakShapeMem` §8).  THE REASON THEY NEED IT is worth
    keeping: `execute_LOAD` ends in `vmem_read … >>= λ w, match w with … | Err e
    => returnM e end`, and `vmem_read : M (result _ ExecutionResult)` — so the
    value returned on the error path is an `ExecutionResult` THE CONE
    PRODUCED, and `gwx` demands `exres_wf` of it.  Cheap, because `gwp`'s bind
    rule takes plain `gwalk` for the PREFIX: only the clause spine is walked.
  - both generator modes regenerated (`make gen-shape`, idempotent); the
    294-lemma tower and the 116-lemma value sweep came back green with **no
    proof-script change** — the predicate they prove changed, the solver did
    not.  Tower ~5 min serial, value sweep ~7 s, `WeakShapeMem` 28 s,
    `WeakShapeExec` 57 s, `WeakShapeTop` 1 s.

## FINDINGS (2026-08-14, C8 — machine-checked)

- **(O11) A LEAF TACTIC'S UNGATED `exact I` IS THE (O8) TRAP AGAIN, ONE LEVEL
  DOWN.**  `gw_leaf` starts with `exact I`, which is free while arguments are
  variables and RUINOUS once they are not: inside `checked_mem_read`'s
  misaligned-split `untilMT` body, `gwalk (liftR (mmio_read …))` measured
  **216 s** and `within_mmio_readable` **76 s**, because `exact I` whnf-evaluates
  a COMPUTING callee at concrete address/width arithmetic once per visit.
  Naming the callee (`apply gwalk_liftR, gw_mmio_read`) makes both ~0 s; the
  loop body went 288 s → 0 s and `checked_mem_write`'s twin from "not finishing
  in 7 min" to 0 s.  C5's prescription (hand-structure the loop) was right; the
  REASON is this, and the rule is: **in a hand script over the memory cone,
  name every callee — never let the generic leaf see a computing term.**
- **(O12) `Defs.returnR` is missing from the sweep's `cbn` list.**  Harmless to
  the generated sweep (a fresh variable at a fault-match join costs nothing),
  fatal to a hand script that must keep a value's identity across the join —
  the next `intros` then names the join's fresh variable instead of the pair.
- **(O13) `gwx_step`'s value-carrying bind rule keys on the prefix type being
  literally `ExecutionResult`**, so at a `result _ ExecutionResult` prefix it
  falls through to the value-irrelevant route and silently DROPS the
  postcondition; the symptom is a stranded `gwp _ _ (early_return (Err e))`
  goal four steps from the cause.  `WeakShapeMem` §8's `gxr_step` is the fix.
  Same genre as C7's trap (ii): a rule that falls through instead of failing
  turns a missing hypothesis into a mystery goal.
- **`tools/lemma_diff.py` HAD A FALSE-NEGATIVE BUG, FIXED HERE.**  Its
  proof-blanking regex treated the `Proof` in `Set Default Proof Using "Type".`
  as a proof opener, so everything up to the file's FIRST `Qed` was blanked in
  both revisions — i.e. any declaration deleted in that window was INVISIBLE.
  It surfaced only because C8 moved the first `Qed` a hundred lines down and
  the tool started reporting a lemma that is still there.

## What REMAINS in this effort (after C8)

1. **LIVENESS, and it is not a `∀ b` fact.**  `∀ b, sail_live (riscv_step b)` is
   refuted by (O9)'s witness; its honest form is `sail_live` under a
   REGISTER-STATE PRECONDITION (xv6 runs with the H extension off, so
   `cur_privilege` is never `VirtualSupervisor`/`VirtualUser`).  **Settle that
   precondition FIRST** — it decides the statement, and only then is a `gok`
   tower worth generating (finding (O7): one pass, every mode).  Behind it:
   the ~100 `exit`/`internal_error`/`assert_exp` reachability sites of (O3) and
   the misaligned-split loop's termination.  Everything the shape half built
   transfers — the tower's shape, the peel, the cone's layering — except that
   `glive` composes through none of it for free.
2. **The three axiom facts** (`rv64d_axiom_shapes`) are the shape half's whole
   remaining assumption.  They are one line each and irreducible in Coq; the
   only way to remove them is to DEFINE `load_reservation`/
   `cancel_reservation`/`plat_term_write` in `model-xv6iris/riscv_extras.v`,
   which moves the same assumption into the model.  Decide deliberately.
3. **NOT IN SCOPE, and never was**: the genuine robustness conditions
   (`edges_split`/`ee_ok`/`bytes_ok`/`bad_wf`/`Hcq`/`Hseip`), the MMIO seam
   (`cone_liftable`, now carrying `dev_ok_blk` + `fused_blk`) and
   `xv6_block_cover`.  Those are DISCHARGE CAMPAIGNS (static checker + Iris
   discipline exports + 6c pinnedness, M5), not eliminations.

Keep the tree green per commit; findings in commit messages and here.
