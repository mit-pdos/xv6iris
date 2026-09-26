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

## SY1 -- the silent alternative leaves the file lines

- [ ] **SY1-map** (read-only): the exact consumer map of `lmh_noc` and of
  (A)-(D) in design §2; which children pay `ushf_wq`'s left arm and why;
  whether the fork re-entry's whole-lend row is refutable; whether (C)/(D)
  are reached at the union or only by the pipeline/seccomp shapes.
- [ ] **SY1a** (pure): split `lmh_noc` into `lmh_pad` (total) and `lmh_sil`
  (optional); instances; `GenOutPure` pad re-pointed; `ralt_ok` drops
  `REcho 2`/`RFSilent`/`RCSilent`; decider re-checked; the negative demo
  `echo a > f; echo b > f; cat f` -> `a` refuted.
- [ ] **SY1b** (proofs): (A) PEND at the credential's own alternative; (B)
  the re-entry row refuted, children paying at their own alternative; (C)/(D)
  at `lmh_sil` or a named alternative.

## SY2 -- the `sync` line

- [ ] model (`LSync`, three alternatives, admission, decider, demos)
- [ ] the sync entry at the union registry, paying PEND at RAN
- [ ] sh's round at `LSync`

## SY3 -- the durability link (design §4-§5)

- [ ] the trajectory witness (unsynced half; no kernel change)
- [ ] K1 the receipt's statement; K2 arm 22; K3 the durable copy's tie
- [ ] the boot relation with the floor; the negative demo across a crash
