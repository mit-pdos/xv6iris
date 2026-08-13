# Shrinking the capstone's premise ledger — worklist

**Status (2026-08-13): IN FLIGHT (stage C4 landed; C5 is the shape sweep's
remaining tower + residue).**  Follow-on to
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

## What C5 owes (unchanged in kind, one obligation smaller)

1. **The generated tower, to 294** — raise `gen_shape.py --limit`, shard so
   each stays under ~10–15 min, add to `_CoqProject`, and budget a serial
   multi-hour chain (they cannot be built in parallel).
2. **The 47-function residue**, hand-proved in topological order; three of its
   obligations are semantic rather than syntactic: `0 < split_width` in
   `checked_mem_write` (the Sail precondition `0 < width ≤ 4096` travelling
   down through `split_misaligned`, which returns `width` itself on the
   unsplit path), the fuel recursion `_rec_pt_walk`, and the exclusive window
   carried from `checked_mem_read`'s `read_ram` to `checked_mem_write`'s
   `write_ram` through `catch_early_return`/`liftR`/`untilMT` (the escape
   index `gwalkx`/`gsilent` of `WeakShapeOverrides` §3 is what composes it).
   C4's fix removed one item from this list: a standalone conditional write
   no longer needs a window at all.
3. **The three axiom facts**, consumed inside 2 at `vmem_read_addr`,
   `execute_STORECON` and `htif_store` via `WeakShapeTop`'s
   `gw_*`/`gsilent_*` lemmas — after which the capstones can take
   `rv64d_axiom_shapes` in place of the two `∀ b` premises.
4. **Liveness (O3)** — still behind the ~100 `exit`/`internal_error`/
   `assert_exp` reachability sites, plus the misaligned-split loop's
   termination (`N ≥ 1` from `split_misaligned`).

**Next stage (D-C5).**  (O4)'s spec fix LANDED in C4; the ordered list above
is what is left, and item 1 is a scheduling problem rather than a proof one —
plan the serial shard chain first, because nothing above the memory cone can
be stated until it exists.

Keep the tree green per commit; findings in commit messages and here.
