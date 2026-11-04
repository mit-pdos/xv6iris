# E-a2 progress — the CONTENDED RUNTIME-BORN LOCK on track (a), dead set empty

Brief: ~/dev/weak-orch/promising/Ea2_prompt.txt (owner ruling [OWN.P13], context.md item 20; G4-review2.md §1
note 3, §6 A-3′, §7).  PASS = (1c)-style mutual exclusion (per byte) for BOTH acquirers + (4)'s "field never reads
junk/image", at `Dd := fun _ => False`, 0 named inputs, ≤ 2k new lines (hard stop 3k).  New files only: OwnAE2*.lean.

## Status (top): DONE — PROVED (2026-11-04); lines 2,206 (10% over the 2k target, under the 3k hard stop)
- THE VERDICT `own_e2` (Weak/Prom/OwnAE2.lean): `∀ M run, validRun (xStep xs5) img5 () (progs t5) M run →
  ∀ h, q5 M (run.trace h)`, `q5 = qLk3 ∧ qGd` — (1c)'s per-byte mutual exclusion over the text-shaped field stores
  of ALL three harts (both acquirers), and (4)'s "every byte of every field load has a good source" (a text-shaped
  field store that is hart 0's initialisation 5 or an acquirer's: never the image, never `kfree`'s junk).
- Through `adequacyA` at `Dd := fun _ => False`, protocol `π4`; `#print axioms own_e2`: propext, Classical.choice,
  Quot.sound.  0 named inputs.  No free mode, no deadInv.  Build: `lake build Weak.Prom.OwnAE2` green (294 jobs).
- New files only (namespace `Weak.Prom.OA.E2`); no existing file touched; no root edit.
- Lines: Defs 448, Lock 386 (the re-split + the birth-aware acquire), H0 333, CS 501, H1 360, verdict 178.
  Of these ≈ 0.6k is the new mechanism (owners/classes/resources of the runtime lock, `resplit5`, `hclaim5`,
  publication slot, `l2_byte5`/`chain5`/`claim5`/`acq5`); ≈ 1.6k is per-text proof (copy-adapt of E-a's (1c)
  critical section/loop and (4)'s hart 0 for the new text, the verdict's trace lemmas, the setup).

## How the re-split works (`resplit5`, OwnAE2Lock.lean)
- Boot: hart 0 (the page's owner) holds the `pend` and claim token of EVERY message touching L2's word (any shape,
  author, content).  At its INITLOCK store `b` it takes `b`'s pend (fulfil) and turns the bag ABOVE `b` into the
  persistent `lkB5 b`: release-shaped words → `rSlot5 r` (pend inside, as (1c)'s release slots); anything else that
  is not acquire/release-shaped → `lkJunk`; and, partitioned BY AUTHOR for every hart `h < 3` of the machine,
  `hSlot5 h b := inv (obg h b 0 ∨ token (ak h b))` — `h`'s acquire words' pends and lock words' tokens above `b`.
- `ak h t`: one boot token per (hart, timestamp), each hart holding its own family (pre-allocated, plan R-a5 style).
  A hart claims its part of the lock born at `b` once, with `ak h b` (`hclaim5`).  No acquirer identity is used:
  every hart is offered a part; hart 0 never claims its own.
- `b`'s own resource (the field's points-to at `c` + the cpu field's bag, naming the runtime `γ`) is (4)'s DEFERRED
  saved-proposition deposit at the publication; the handle `isLockAt` + `lkB5 b` is deposited PERSISTENTLY in the
  publication's slot (any number of readers — the two-readers issue of a one-shot slot does not arise).
- Acquire (`acq5`): the read floor covers `b` (publication view), so each byte's source is `b`, an acquire or a
  release word above `b` (junk above `b` / the flag's junk are fulfilled yet hold their pend: absurd); atomicity
  (`chain5`) as (1c) with the claimed own bag; the claim opens `b`'s saved-prop slot or a release slot.

## Findings / S5 consequences
- A-3′ does NOT kill: the re-split is generic (no program fact), needs no acquirer identities, and fits in one
  lemma (≈ 85 lines) plus a per-hart claim (≈ 15).  Cost driver is the per-text proof, not the mechanism.
- New S5 obligations it exposes: (i) each hart carries, per lock it has joined, its own-message bag (a per-CPU
  map lock ↦ bag in the hart's resources); (ii) the per-(hart, t) claim tokens `ak` are a new boot family;
  (iii) LOCK DEATH / REUSE (kfree of a struct holding a lock, then a new initlock at the same address) is NOT
  covered: the classification "above `b`" is unbounded, so a second birth `b'` would need the pends above `b'`
  that sit in the first lock's parts — S5 needs the window `(b, next birth/death after b)` (a pure function of
  the final M, fine on track (a)) or a death protocol that collects the parts back; (iv) inherited from E-a (4):
  the birth class `bth`/`bthAt` is "hart 0's plain zero word at `Lk`" and the lock address is a classification
  constant — S5 needs them keyed by the owner/address of the initlock; (v) the hart count (3) appears in the
  author partition (`lmS`, `List.range 3`) — NCPU in S5.
- Test choice: publication through a release WORD (image 1 at `Z`, hart 0's `sw zero` after `fence rw,w`; readers
  `lw; bnez; fence rw,rw`, xv6 `main.c`'s `started` shape with polarity inverted), so hart 0's text is (4)'s `p4o`
  verbatim and `π4` is reused.

## Files (Weak/Prom/, namespace `OA.E2`)
- `OwnAE2Defs.lean` (448) — test `t5`/texts `p5h` (+ (4)'s `p4o`), classes (`fPub`, `fJ`, `isA2`/`isR2`/`isJ2`,
  `isC3`, `isPO`), the trace invariant `q5` (`qLk3`, `qGd`) and lemmas, bags `obg`, resources `cPts5`, `pPts5`,
  `Rs5`, `Rb5`, slots `rSlot5`, `hSlot5`, protocol `lkB5`, publication `Pub5`/`fSlot5`, boot context `ctx5`.
- `OwnAE2Lock.lean` (386) — `resplit5`, `hclaim5`, `fdeposit5`, `fclaim5`, `jk_front`, `l2_byte5`, `chain5`,
  `claim5`, `acq5`.
- `OwnAE2H0.lean` (333) — hart 0: `h0_hart5` (junk), `h0_sdj5`, `h0_birth5` (INITLOCK: γ + re-split),
  `h0_tail5`, `h0_pub5` (deferred deposit + publication).
- `OwnAE2CS.lean` (501) — `cld3`, `cpu1_5`, `cs1_5`, `cs2_5`, `cpu0_5`, `rel5`.
- `OwnAE2H1.lean` (360) — `floop5` (publication wait + claim of the hart's part), `loop5` (contended L2 loop).
- `OwnAE2.lean` (178) — `setup5`, `premise5`, THE VERDICT `own_e2`.
