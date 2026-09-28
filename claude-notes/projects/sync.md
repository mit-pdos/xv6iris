# Worklist: `sync` in the union -- DONE; open cleanups only

Design: [`../design/sync.md`](../design/sync.md).  Order is the owner's:
the silent alternative goes first (it is the prerequisite for any negative
demo, and it closes the landed within-era hole), then the line, then the
durability link.

## Rules

- Every landing keeps `UInitUnion.union_adequacy_closed` closed and the
  three audits at the baseline (system 13, tree 13, union 14); whole-tree
  gate on the VM before every landing; commit and push to `main` at green
  checkpoints (owner, 2026-09-26).
- One lane per cone at a time; independent lanes (disjoint files) run in
  parallel in separate worktrees with separate remote trees.

## DONE (2026-09-28, branch `sync3-a4`)

Every lane landed; the narrative and the lane plans are in
[`../completed/sync.md`](../completed/sync.md), the design of record in
[`../design/sync.md`](../design/sync.md).  What is left is cleanups, none
blocking.

## Open cleanups

From SY1:
- pipelines' `PLRun []` still in `PipesDisc.plsafe` (reaches the N-stage
  layer: `PipesView.pv_ok`, `PipeOutNEv.pwc_blkV_file_empty`);
- `LineModelLinks.lm_ab_noc`/`lm_apr_noc`/`lm_ab_noc_len` have no users;
- the user-tier LOAD/STORE leaves carry an in-page premise redundant with
  alignment (`WpUmodeLoad`, `UkLoad`, `UkLoadText`, `UkStore`,
  `WpUmodeStore`) -- the fetch clause's twin, which the owner had removed
  from `uinstr`; ask before touching;
- `UInitTreeBoot.v`'s header cites a lemma `tree_cc_wb_conj8_is_turn_to_taint`
  that does not exist.

From SY3-A4:
- unused after the switch: `GenOut.gdrain_ret_good`,
  `PipeOutNEv.lm_good_out_of_stage_open` and `GenOutWild.lm_good_out_wild`
  (their `_pad` twins are the ones used), `UnionAdm.usync_last_round`,
  `UShURoundDefs.upend_sync_record` (with `usync_at_round`, which only it
  uses);
- `union_led`'s separate `union_floor` row is read only at a tainted
  PowerOn (the conclusion's own floor is inside `union_phi_res`); it could
  fold into the taint arm;
- `UnionAssumptions.v` prints `union_adequacy_closed` only; the corollary
  `union_sync_cut_neg` adds `sa_disc` and `demo_sync_cut_neg`, both closed
  under the global context (checked by hand at A4), so its assumptions are
  the theorem's.
