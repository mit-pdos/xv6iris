# E-a progress — deciding experiment for G4 (track (a) with the dead set EMPTY, no free mode)

Brief: ~/dev/weak-orch/promising/Ea_prompt.txt (owner ruling [OWN.P11] "G4. Do B"; G4-review.md §6 condition 1).
PASS = (1c) + (4) + one racy non-holder read, all with `Dd := fun _ => False`, 0 named inputs, ≤ ~4k new lines.

## Status (top): DONE — PASS (2026-11-04).  All three proved, dead set empty, 0 named inputs, 3,759 new lines
- `own_lock1cE` (+ `own_lock1cE_excl`) OwnAE1c.lean — statement of `own_lock1c`; π = `π1c`.
- `own_holdE` OwnAEHold.lean — statement of `own_hold`; π = `π3`; the NON-HOLDER racy read by ⟦t⟧ (`pc_readE`).
- `own_pipeE` OwnAEPipe.lean — statement of `own_pipe`; π = `π4`.
- All through `adequacyA` at `Dd := fun _ => False`; `#print axioms`: propext, Classical.choice, Quot.sound.
  No deadInv/dead_doom/doomD/free mode in any E file (grep: only docstrings mention them).  New files only.
- Build: `lake build Weak.Prom.OwnAE1c Weak.Prom.OwnAEHold Weak.Prom.OwnAEPipe` green (293 jobs).
- Lines: Base 141; (1c) Defs 380 + CS 487 + verdict 459 = 1,326; racy read 533; (4) Defs 447 + H0 385 + CS 299 +
  H1 457 + setup/verdict 171 = 1,759.  (Originals: (1c) 1,944, (3) 727, (4) 2,866 — the E versions are smaller:
  no free walkers, no dead classification.)

## Findings
- Free mode was needed ONLY because content-classified dead messages had no owner.  With an owner for every
  message's `pend` (per byte, from boot), ordinary R-a1 doom is enough: the doomer is the owner and keeps every
  other resource; a NON-owner never dooms.
- Non-owner / protocol-violating sources are refuted PURELY by the core's guard: `grd_self` gives `⟦t⟧ π.okMsg M[t]`
  per byte; the hart branches on the actual value and, in the excluded branch, carries `⟦V⟧ False`, which discharges
  its trace obligations (guarded Ψ) while it keeps fulfilling its own writes from its own bags.  `frontA`'s `Valid`
  part is never used; its `shot` part refutes fulfilled junk / own-bag messages.
- Lock words: the lock protocol owns them (acquire AMOs → author's bag, release words → release slots, anything else
  → `lkJunk`, an invariant holding the `pend` forever, refuted only when seen fulfilled below the frontier).
- (4): hart 0 owns the field and the L2 word at boot (including hart 1's FUTURE AMO/release messages); the word's bag
  above the birth moves to hart 1 through L1's publication; R-a4 and L2's atomicity (`nxtL b ts`) follow from that
  ownership alone (no content class, no `exclOk`).  One acquirer: the word's bag moves wholesale.
- π obligations at stores are trivial for the litmus texts (shape facts).

## S5 consequences (see the report)
- Drop "replacing free mode 2–4k"; replace by: per-location protocols for racy-read fields and lock words, with an
  okMsg obligation at EVERY kernel store (alignment facts).  `Proto.okMsg` is message-local (no timestamp), so a
  lock word's protocol cannot say "after the birth"; the usable form is "no message spans a lock word and a
  non-lock byte" (true for aligned ≤8-byte stores, incl. `kfree`'s byte memset), not (4)'s "4-byte at the word".
- A CONTENDED runtime-born lock needs its word's bag re-split at initlock into (1c)'s lock-protocol slots (not built).

## Design (as built)
- Dead set empty: adequacyA at `Dd := fun _ => False`; free mode unreachable (`fulT_shot`); no deadInv/dead_doom/doomD.
- Per-byte owners: lock word bytes → the lock protocol (acquire AMO → author's bag, release word → release slot,
  anything else → `lkJunk`, which is never opened to doom, only refuted when seen fulfilled below the frontier);
  data bytes → the points-to (pend of EVERY later message touching them, any shape/author/content);
  rest → boot owner (kept, unused).
- Protocol π (core ⟦t⟧ facts): "a message touching a lock word is a 4-byte message at the word"; used to refute a
  data read from a lock-owned straddling message by the guard `⟦t⟧ False` (local, keeps every resource).
