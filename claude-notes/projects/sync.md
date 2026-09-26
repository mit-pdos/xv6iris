# Worklist: `sync` in the union

Design: [`../design/sync.md`](../design/sync.md).  Order is the owner's:
the silent alternative goes first (it is the prerequisite for any negative
demo, and it closes the landed within-era hole), then the line, then the
durability link.

## Rules

- Every landing keeps `UInitUnion.union_adequacy_closed` closed and the
  three audits at the baseline (system 13, tree 13, union 14); whole-tree
  gate on the VM before every landing; commit and push to `main` at green
  checkpoints (owner, 2026-09-26).
- One lane at a time.

## SY1 -- DONE: xv6 d66e41c, no silent alternative (design §1-§2)

Open cleanups it left, none blocking:
- pipelines' `PLRun []` still in `PipesDisc.plsafe` (reaches the N-stage
  layer: `PipesView.pv_ok`, `PipeOutNEv.pwc_blkV_file_empty`);
- `LineModelLinks.lm_ab_noc`/`lm_apr_noc`/`lm_ab_noc_len` have no users;
- the user-tier LOAD/STORE leaves carry an in-page premise redundant with
  alignment (`WpUmodeLoad`, `UkLoad`, `UkLoadText`, `UkStore`,
  `WpUmodeStore`) -- the fetch clause's twin, which the owner had removed
  from `uinstr`; ask before touching;
- `UInitTreeBoot.v`'s header cites a lemma `tree_cc_wb_conj8_is_turn_to_taint`
  that does not exist.

## SY2 -- the `sync` line

- [ ] model (`LSync`, three alternatives, admission, decider, demos)
- [ ] the sync entry at the union registry, paying PEND at RAN
- [ ] sh's round at `LSync`

## SY3 -- the durability link (design §4-§5)

- [ ] the trajectory witness (unsynced half; no kernel change)
- [ ] K1 the receipt's statement; K2 arm 22; K3 the durable copy's tie
- [ ] the boot relation with the floor; the negative demo across a crash
