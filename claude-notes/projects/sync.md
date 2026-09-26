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

## SY1 -- the bump to d66e41c, and the silent alternative out (branch `sync-bump`)

RULED (owner): option (b), sh checks malloc; upstream `d66e41c`.  The bump
and the model change land TOGETHER (the image prints `out of memory` where
the pinned model has no such output), so `sync-bump` is red until the end;
merge to `main` when the whole tree and the audits are green.  Design §2.

- [x] **SY1-map** (read-only): the consumer map (findings folded into design §2).
- [x] **SY1-pin**: `XV6_REV` d66e41c, `make dump-force`; only sh's dumps and
  `FsImgRaw.v` moved (`dff753bee`).
- [ ] **SY1-U** (the user-image relayout): sh's catalogs (`tools/ucode_sh*.txt`
  re-derived, `cmdalloc` catalogued, `make gen-ucode`), every sh pc/data/
  immediate/size literal remapped (playbook §1 "THE USER-IMAGE RELAYOUT"),
  `cmdalloc`'s walk and the five constructors' reshaped walks, the NULL
  arm stated as an ABSTRACT continuation at `panic("out of memory")`.
- [ ] **SY1-M** (pure): `ROom` at every forked line shape; `REcho 2` only at
  `LEcho []`; `RFSilent`/`RCSilent` out; `lmh_noc` optional, the pad on
  `lmh_exf`; the decider; demos, including the NEGATIVE `echo a > f; echo b
  > f; cat f` -> `a` (refuted again once the OOM death prints).
- [x] **SY1-P** (proofs): the child's OOM law (print, file `ROom`, pay `Wc I
  0`) discharging SY1-U's continuation at every child; `ushf_wq`'s left arm
  gone; the fork re-entry's whole-lend row refuted; PEND at the block's own
  alternative; audits 13/13/14.  Findings: (i) `ushp_oom`'s lend must carry
  the child's LEDGER (panic writes fd 2), so the child walks pass `Cr ∗ ustd
  ld`; (ii) the blank-line arm is the TAINT's (the read's clean arm
  delivers an admissible line, never newline-first), so no `Wc I 3 -∗ Wc I
  0` law survives anywhere and `REcho 2` at `LEcho []` has no proof use;
  (iii) the node-0 pipeline OOM budget fits because a pipeline has at most
  15 stages (`UShUPipes.upls_fs_le15`).

## SY2 -- the `sync` line

- [ ] model (`LSync`, three alternatives, admission, decider, demos)
- [ ] the sync entry at the union registry, paying PEND at RAN
- [ ] sh's round at `LSync`

## SY3 -- the durability link (design §4-§5)

- [ ] the trajectory witness (unsynced half; no kernel change)
- [ ] K1 the receipt's statement; K2 arm 22; K3 the durable copy's tie
- [ ] the boot relation with the floor; the negative demo across a crash
