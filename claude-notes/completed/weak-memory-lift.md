# The lift gap (seam 1): WeakLang ↔ wp-machine — COMPLETE (2026-08-13)

**Outcome.**  `WeakComposeLang.xv6_weak_robust_lifted` / `_adequate` are
the capstone adequacy-over-RVWMO compositions: `Print Assumptions` for
both is EXACTLY the 5 rv64d baseline axioms (`load_reservation`,
`match_reservation`, `cancel_reservation`, `valid_reservation`,
`plat_term_write`) — no funext, no classical axiom.  `xv6_block_cover`
is DELETED, `pf_violation_free_hart` is consumed nowhere on the live
route, and φ enters ONLY through `weak_system_adequacy_phi`'s
WeakLang-level `no_violation`, at instruction granularity, where it is
actually provable.  The M6 statement over the old premise
(`WeakCompose.xv6_weak_robust`, `m6_side_conditions`) is kept as the
archived form; `WeakCompose.v` §6 records the supersession.

## The two findings (read these before touching the seam again)

1. **`pf_violation_free_hart` / `xv6_block_cover` are REFUTABLE at event
   granularity, not merely unproven.**  A pf run can park an author
   mid-instruction between its walker A/D CAS (a mid-block `WCexcl`
   append) and its release-pending (`w_relp`) data store; a foreign hart
   observing through the dangling CAS gives a REAL pf-reachable hart
   violation that NO instruction-atomic WeakLang run exhibits (the
   author's instruction either didn't CAS or also published).  So the
   φ-consumption cannot go through "any violating pf run has a
   block-atomic witness"; it must go through the minimal-bad-edge cone,
   under premises that pin cross-edge sources to block-last events.
   (Same rank as L3's DMA-author finding; both live in
   `WeakComposeLang.v` §B.)
2. **Same-agent fulfil timestamps are NOT program-order monotone**
   (`store_post` raises `w_vwOld`/`coh`, not `w_vwNew`, so `fulfil_ok`
   orders only same-byte stores).  In-block trace ordering of the
   dependency graph (`WeakRobustCone.gdep2_sa_lt`) therefore needs
   `ee_ok`'s gE arm — luckily already in the exhibit context.  Any
   future argument that quietly assumes "later in program order ⇒ later
   timestamp" is wrong.

## What landed, stage by stage (branch `weak-memory`)

- **L0–L3** (see the plan section below): DMA-tid/mip-oracle/log-pub/
  PDisk unifications; `WeakRobustBlocks.v` (cone-cut + completion under
  `img_total`); `WeakSailLTS2.v` (the ⇐ bracket, `sail_block`,
  `cls_canon`/`rmw_tight`); `WeakComposeLang.v` v1 (regrouping,
  φ-consumption modulo `xv6_block_cover`); the hart-restriction fix
  (`violation_hart`).
- **B2 `WeakSailComplete.v`** — the sail-level completion kit.  The
  free monad has no nat measure, but none is needed: `mchild`/`macc`
  give `Acc`-well-foundedness of the (transitive) subterm order on
  `iMon` (a structural `Fixpoint` producing `Acc`, destructing the ∃ in
  Prop), which drives `quiet_complete` (silent/fence epilogues; appends
  nothing) and `tail_complete` (finish an in-flight instruction with
  free values: `read_latest_*` under `img_total` for RAM,
  `oracle_consistent`'s ∀-paths form for device non-stuckness, classes
  chosen CANONICALLY so `cls_canon` holds by construction).  Plus
  `pf_local_commute`/`pf_run_insert_local` (quiet solo steps commute
  across other agents).  FINDING: `sail_shaped` does not imply
  non-stuckness — `GenericFail`/`Discard`/`ExtraOutcome` have
  empty/abstract result types, making its ∀-arm vacuous while
  `sail_mstep` is stuck — hence the sibling predicate **`sail_live`**
  (and both `quiet_tail`/`sail_live` exclude `ChooseReal`, whose
  inhabitation would drag Stdlib's classical-reals axiom into the
  footprint; rv64d emits none of these).
- **B3 `WeakRobustCone.v`** — the block-contiguous cone replay,
  abstract over `(P, bnd)`.  `Qcfg_step` (a step-exporting twin of
  `Qinv_step`); block vocabulary; cross-sources are block-last-memory
  (from the `cross_src_last` premise) and cross-targets are memory
  events; **contracted-block acyclicity is DERIVED from event-level
  cone acyclicity** (a contracted cycle closes into an event cycle
  through gpo, because targets sit at-or-before their block's
  cross-source) — no timing argument, no new premise;
  `bad_edge_violates_blocks` = the exhibit's violating configuration
  reached by a block-contiguous order, with the per-event `cstep` chain
  and per-prefix `qcfg` exported.
- **B4 `WeakSailCone.v`** — the pxv6 instantiation: `pbnd`/`pquiet`,
  the state-level premise `cross_src_quiet` ⇒ trace-level bridge
  (`pquiet_step`), cut-state classification (`cut_pquiet`), the
  psail↔pxv6 transport (`hlink`/`prj_cfg`/`pf_step_lift`), and the
  completions applied (`xquiet_complete`/`xtail_complete`).
- **B5a (same file)** — `cone_segments2`: the fully segmented violating
  run (`SegHart`/`SegIrq`/`SegDisk`, `chained2`).  The splice is a
  SINGLE PASS (`seg_build` walks the chain re-taking steps via
  `wp_pf_step_transplant`, running each finished agent's epilogue at its
  last step's position; the enabling fact — at most ONE agent is ever
  mid-block — comes from `done_full_contig`).  `rmw_tight` at replayed
  steps is DERIVED (`own_coh` + `pf_rmw_latest`), not premised;
  `cls_canon` via `Hcls` + `w_relp`'s σ-independence + the fact that a
  writing label's class is determined by the pre-state
  (`pxv6_class_det`).
- **B5b `WeakComposeLang.v` v2** — the rewire.  pxv6→psail projection
  (`pf_xsolo_prj`, paying the `cls_canon`/`rmw_tight` residue rather
  than assuming it); `seg2_refine` (cut multi-instruction hart segments
  at interior boundaries); **`wl_lift`** — the WeakLang lift with the
  device seam as per-segment constructor premises and the successor
  CONSTRUCTED from the reconstructed `wrun` (so the old `hart_dev_seam`
  ∀-quantifier is retired); `xv6_no_bad_edge` (φ refutes every bad edge
  through the cone); `robust_main_no_bad` + `gdep2_acyclic_bad_free`
  (`∀ ¬bad` makes `bad_wf_strong` vacuous) replace the
  `pf_violation_free_hart` consumption; the two capstones re-stated
  with the same names and conclusions.

## The final premise ledger (beyond `main_premises` + the 5 axioms)

Per traced bundle (`xv6_cone_premises TS`), all trace-level, all in the
D-M6-8 static-discipline epistemic slot:

- `Hcq` (cross_src_quiet): every cross-`gdep2`-edge source's post-state
  has a quiet residual (`pquiet`: hart — no further memory access before
  the boundary; disk — empty emit buffer).  Kills the dangling-CAS
  corner AND gives block-contract acyclicity.  xv6 story: kernel PTEs
  are A/D-canonical (kpt-share) so walker CASes touch only user PTEs;
  6c's pinnedness discipline covers software/walker races there.
- `Hres`: every in-flight hart record's residual is `sail_shaped` ∧
  `sail_live` ∧ oracle-consistent for some device state (derivable in
  principle from block-start facts + the step-preservation lemmas in
  `WeakSailComplete.v`; premised in record form for simplicity).
- `Hirqb`: an `irq_deliver` trace step has a `pbnd` pre-state
  (deliveries sit between blocks).  Upgrade path: a generalized
  `sail_block_wrun` tolerating mid-block deliveries whose post-delivery
  events never read `sig_seip` (xv6's only mid-block sip access is
  devintr's `w_sip(r_sip() & ~2)`, whose SEIP bit is dead in the
  written value).
- `Hcls` (cls_canonical): each logged message's class is `lbl_class` at
  its fulfil's pre-record (the full machine's class binder is free; the
  kernel image's stores make it canonical — no release stores; `w_relp`
  from fences).
- Global: `img_total (wgimg g0)` (boot image covers RAM — `wlat_init`);
  `∀ b, sail_shaped (riscv_step b)` and `∀ b, sail_live (riscv_step b)`
  (seam (6), decoder-checkable); `cone_liftable` — the per-segment
  device seam (hart oracle streams consistent with the wl fabric, the
  plic wire value, the disk's `wa_dd = wgdev` + true-flat
  `wdisk_step`), i.e. the retained MMIO/M5 assumption of §6 (4) in
  per-decomposition form; and (adequate form) the pool's WP package,
  which is where the Iris-side work (phi-upgrade / SC→weak port) feeds
  in.

## Reusable recipes

- **`Acc` on a free monad**: an inductive with function-typed children
  has no nat measure, but the immediate-subterm relation is
  well-founded by a structural `Fixpoint` returning `Acc` (destruct the
  ∃ in Prop; `k v` is a legal structural subterm), and `Acc_tc` lifts
  to the transitive closure.  This retires "the free monad has no
  structural measure" as an obstacle everywhere.
- **Contracted-graph acyclicity for free**: if every cross edge leaves
  from its block's last relevant event and lands on a relevant event,
  a block-contraction cycle closes into an event-level cycle via gpo —
  derive, don't premise, and don't reach for timestamps (finding 2!).
- **Choose the free binder canonically**: the pf machine's class binder
  is free, so a CONSTRUCTED run can satisfy `cls_canon` by choice; only
  REPLAYED steps need the `Hcls` premise.
- **Splice by transplant, not by commutation**: re-taking steps at a
  config that differs only in finished agents' slots
  (`wp_pf_step_transplant`) subsumes the pairwise-commutation shuffle
  and keeps the config sequence explicit.
- `Require Import SailStdpp.Values` rebinds `++` to `String.append` —
  name what you need qualified instead.

## What remains OUTSIDE this project

Discharging the premise ledger for the concrete kernel: the static
checker family (D-M6-8 / `kernel_discipline`) for `Hcls`/`Hirqb`/shape
predicates; the 6c walk-bridge/pinnedness work behind `Hcq`; the virtio
discipline behind the disk seam; and the WP package (the phi-upgrade
three-state protocol + the M4 SC→weak port).  Those are the
`weak-memory-phi-upgrade`, `weak-memory-porting` and walk-bridge
efforts' worklists, not this one's.

---

## The original plan (for reference)

Goal: `pf_violation_free` disappears from `xv6_weak_robust`'s premise
set, discharged by `weak_system_adequacy_phi` through the lift.  Stages
L0 (breaking unifications: DMA tid `Some n_disk`, `irq_deliver` oracle,
log-based `pub_of`, PDisk burst/emit) — f7e3ed6d; L1
(`WeakRobustBlocks.v`) — 335d999d; L2 (`WeakSailLTS2.v`) — 6b0e6ee6;
L3 (`WeakComposeLang.v` v1) — 117f9014 + b9efdfc8; stage B (the residue
redesign after the refutability finding) — 0f7e61a0 (design),
4b346846 (B2+B3), 8378c5db (B4), 5ad28635 (B5a), 2394dcf3 (B5b).
The three resolved analysis obstacles (granularity / completion
admissibility / publication alignment) are recorded in the L1–L3 files'
headers.
