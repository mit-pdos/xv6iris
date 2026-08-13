# Shrinking the capstone's premise ledger — worklist

**Status (2026-08-13): IN FLIGHT.**  Follow-on to
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

**Fix (stage D, replaces the old batch-B plan's seam handling):**
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
- **C** — the shape-typing sweep discharging
  `∀ b, sail_shaped/sail_live (riscv_step b)` (retires seam (6)).
  Start only after B lands and is green.

Keep the tree green per commit; findings in commit messages and here.
