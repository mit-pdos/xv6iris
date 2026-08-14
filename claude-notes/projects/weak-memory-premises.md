# Shrinking the capstone's premise ledger — worklist

**Status (2026-08-14): IN FLIGHT (stage C6 landed — the DECODER
POSTCONDITION is proven and state-generic, and finding (O9) fixed a
specification bug that had made `∀ b, sail_shaped (riscv_step b)` FALSE; what
remains is the value-carrying window mode, the memory cone, and liveness).**  Follow-on to
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

## What C7 owes

1. **CONSUME the decoder postcondition at `run_hart_active`** — the one
   piece C6 stopped short of, and it is a KIT item, not a proof item.
   `run_hart_active` applies `execute` twice: to `ext_decode`'s output (now
   covered) and to the `ExecuteAs other_inst` REDIRECTION VALUE.
   **PROVENANCE VERDICT (C6, from the sources): every `ExecuteAs` in the
   whole model is produced by a PURE function** — `execute_SINVAL_VMA` and
   the ~60 `execute_C_*` compressed expansions — **and every width in those
   payloads is a LITERAL 1/2/4/8**, so `ast_wf` holds of every redirection
   target.  But `execute`'s monadic clauses have to be shown not to return
   `ExecuteAs`, and no existing predicate can say that: `gwalk`/`gwalkx` are
   value-blind and `gpost`/`gpure` forbid memory events.  What is needed is
   `gwalk`-WITH-A-RET-POSTCONDITION (`gwpx Q P w m` = `gwalkx` with the `Ret`
   arm strengthened), whose bind rule takes `gwalk None` for the PREFIX — so
   **the existing 294-lemma tower is reusable for every prefix** and only the
   ~65 `execute_*` clauses need the new mode.  Design it before writing it.
2. **The memory cone** — unchanged from C5's item 2, and it is the big one:
   ~40 hand lemmas in topological order from `read_ram`/`write_ram` up to
   `fetch` + the eleven `execute_*`.  Three semantic obligations inside it:
   `0 < split_width` (DONE, `WeakShapeOverrides2` §2, given `ast_wf`),
   `pmaCheck` answering `CannotSplit` for exclusive accesses (so
   `split_misaligned` returns `N = 1` — note `split_misaligned`'s
   `do_not_split` is TRUE whenever `splittable = CannotSplit`, so that half
   is one line once `pmaCheck`'s postcondition exists), and the AMO window
   (the read's `(pa, n)` must equal the closing write's, which needs the
   translated address and the width threaded through BOTH `checked_mem_read`
   and `checked_mem_write` — a value-level obligation, i.e. item 1's mode
   again).  `checked_mem_write`'s misaligned-split `untilMT` still needs the
   hand-structured script C5 prescribed.
   NOTE: the whole cone goes through `translate → update_and_write_pte`,
   which issues an exclusive read + conditional write, so **every** memory
   instruction — not just the AMOs — pays the window obligation.
3. **The three axiom facts** — unchanged (`WeakShapeTop.rv64d_axiom_shapes`).
4. **Liveness** — behind (O9)'s liveness half: settle the register-state
   precondition FIRST (see the finding), then the `gok` tower, then the ~100
   reachability sites.
5. `tools/gen_shape.py` should grow a `--mode` flag (finding (O7)); C6's 35
   `gpure` lemmas were written out by hand because the cone was small, and
   item 1's ~65 will not be.

Keep the tree green per commit; findings in commit messages and here.
