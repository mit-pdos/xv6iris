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

## SY1 -- the silent alternative leaves the file lines (ON HOLD)

SY1-map DONE: the silent alternative is HONEST -- sh's child dies of OOM in
`parsecmd` (malloc NULL, store fault, kernel-UART message) and sh prints
`$ `; design §1.  Owner ruling pending between (a) `/sync` prints, (b) sh
checks malloc, (c) a memory-capacity refutation.  The map's other findings,
kept for whichever route needs them: the pad can use `lmh_exf` (ok/free/
nopanic already); `uWcf0_of_pre_line_id` can file PEND at its own `a`
(`lm_aprs`); the fork re-entry's whole-lend row is refutable inside
`wp_kshf_fork_core` (its `r ≠ -1` is discarded there); `gprompt_dollar`'s
settled arm is dead at the union; `gwc_line_of_blk0` is reached only under
taint; `UnionDecU.u_canon_name` needs a non-merging pad output.

- [x] **SY1-map** (read-only): the exact consumer map of `lmh_noc` and of
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
