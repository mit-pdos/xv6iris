# E-a4 progress — the LOCK LIFECYCLE on track (a), dead set empty

Brief: ~/dev/weak-orch/promising/Ea4_prompt.txt (owner ruling [OWN.P14], context.md item 21; G4-review3.md §1, §5
A-3″, §6 item 1).  PASS = (1c)-style mutual exclusion and (4)-style no-junk in EACH lifetime, `Dd := fun _ => False`,
0 named inputs, ≤ 2k new lines (hard stop 3k).  New files only: OwnAE4*.lean (namespace `Weak.Prom.OA.E4`).

## Status (top): PROVED — but 3,235 lines, OVER THE 3k HARD STOP (2026-11-05)
- THE VERDICT `own_e4` (Weak/Prom/OwnAE4.lean): `∀ M run, validRun (xStep xs7) img7 () (progs t7) M run →
  ∀ h, q7 M (memEv (run.trace h))`; `q7 = qMx ∧ qGd`: per critical section (a field load immediately followed,
  among memory events, by a field store) every loaded byte came from the latest text-shaped field store below the
  store (1c), and every field load reads a good store — never the image, never kfree's junk (4) — across BOTH
  lifetimes of the lock.  Through `adequacyA` at `Dd := fun _ => False`, protocol `π7`.  `#print axioms own_e4`:
  propext, Classical.choice, Quot.sound.  0 named inputs (`hnoinv` is the front end's `x_noInvalT`).
- Build: `lake build Weak.Prom.OwnAE4` green (300 jobs).  `tools/ci/lint.sh`: only `drift` findings, one per new
  file (not reached from a root — no root edit, per the rules; the coordinator wires them).
- The two SEMANTIC kill conditions do not fire: no program-specific fact; readers distinguish the birth from a
  release (the birth is the publication's `b`; window zero words have release slots).  The SIZE kill does
  (3,235 > 3,000, +8%).  Breakdown: mechanism ≈ 1.0k (Defs 489: windows, slots, death mark, parts, verdict;
  Lock 527: resplit, death refutation, windowed acquire/claim); text-generic block library 761 (Gen: flag wait,
  acquire loop, cpu field, release with author-chosen deposit, round step — reusable as S5 leaves); per-text
  proof 1,085 (H0 603: kfree/initlock/publication/close, H1 482: critical section + acquirer round); setup +
  verdict 373.  Nothing was compressed to fit (one tactic per line, as E-a2).

## Test `t7` (two lifetimes of one lock at one address; text loops over rounds `k = a3 ∈ {1, 2}`)
- hart 0 (`p0`): `kfree` junk `J` in the lock word (round 2: THE DEATH of lifetime 1) and the field; INITLOCK
  `sw zero,0(s1)` (a birth); field init 5; `fence rw,w; sb a3,0(a2)` (publication byte `Z = k`); waits for both done
  bytes `Z+1, Z+2 = k`; `fence rw,rw`; pipeclose: xv6's acquire (spin loop, `sd a0,16(s1)`), xv6's release
  (`sd zero,16(s1); fence rw,w; sw zero,0(s1)` — the same message shape as its births); next round.
- harts 1, 2 (`pA`): wait for publication `k`; xv6's acquire/release `p1c` around `ld; addi; sd`; `fence rw,w;
  sb a3,0(a6)` (its done byte); next round.  Image all zero.
- Scaffolding vs xv6: the done bytes (xv6's closer learns it is last from pipe fields under the lock); the
  publication byte; field init after initlock (E-a2/(4)'s order; xv6 initialises fields first).

## Design (as built)
- LIFETIME WINDOWS, pure functions of `M` (Defs §4): `noJ b t` (no lock-word junk in `(b,t)`), `inW b t`, the
  DEATH `isD b t` (first junk above `b`), `bey b t` (beyond); `bey_death`: beyond implies above the death.
  "Junk" = touches the lock word, not a 4-byte acquire/release-shaped word by a hart (`isJ2`, E-a2's).
- SHAPE-ONLY SLOTS: (i) birth slots `bSlot` pre-allocated over EVERY plain zero word at the lock address (any
  author; depositor rights with the page owner) — the deferred deposit of the birth's resource; (ii) at a birth `b`
  the re-split allocates release slots `rSl` for every zero word of `W(b)` (by author), content CHOSEN BY THE AUTHOR
  at the fulfil: the protected resource `Rs5`, or the death mark `dM k` (a closing release that keeps the
  resource); (iii) the death's slot `dSl`, fulfilled only with `dM k`.
- Readers: the birth is identified through the publication (`Pub7` carries `b` and `lkB b k`, `k` pinned by the
  publication byte's value); a source at or beyond the death is refuted (`dead7`: the death is below the frontier,
  its slot holds `dM k`, which contradicts the reader's participation one-shot `eP h k`); a window release's
  `dM k` content is refuted the same way.
- PARTS (`prt h b lo`): each hart's own lock-shaped words above `lo` (acquire `pend`s, all claim tokens, and its
  release words BEYOND the window), unbounded above so a participant owns its own writes AT THE STEP (the window
  membership of a write is not decidable then); claimed from `hSl h b k` with `ak h k`, RETURNED through the done
  byte (`Dn7`: part + `eP h k`), and fed with hart 0's own part and the junk remainder into the next birth's re-split
  (`prt_fpt`, `prt_birth`, `resplit7`).  The page bag's remainder (junk beyond the window) stays with the page owner.
- Death mark `dM k` = every hart's `eP h k` given up (persistent, timeless ghost one-shots); round 1 has the empty
  lifetime born at 0 behind it (its death slot and `dM 0` allocated at boot).
- Hart 0's trace obligation is "no field load" (`qs7 M 0 = noLd`); the verdict derives `q7` from it.
- Flag reads after own stores need the forward-bank invariant `fI` (every forwarded byte is the hart's own store,
  below `vwOld`) — a new generic kit fact.

## S5 / S5c consequences (isLock rebuild)
- isLock is per LIFETIME: `lkB b k` (window slots, death slot, parts) + a lifetime-indexed death mark; the
  publication must pin the lifetime (here a value; in S5 a runtime ghost name allocated at initlock and handed to
  each part would do — participation can live in the part instead of a boot family).
- A death protocol is unavoidable: kfree of a lock word needs every participant's participation back.  Here done
  bytes carry it; for xv6 the natural channel is the lock itself (every release lends the part + participation
  back into `R`, the next acquirer takes its own back) so whoever holds the lock at pipeclose holds all others' —
  NOT BUILT.
- Per-CPU per-lock own-message bags (unbounded above, returned at close); shape-only birth slots with page-owner
  depositor rights; `fI` and the wsM/fI abstract-state lemmas belong in the kit.
- Cost: the mechanism is ≈ 1k; the text-generic blocks (761) are S5-leaf material; per-text proof dominates.

## Files (Weak/Prom/, namespace `OA.E4`)
- `OwnAE4Defs.lean` (489) — texts `p0`/`pA`, test `t7`, flag bytes, `π7`, windows, verdict `q7`/`qs7`, parts,
  slots `rSl`/`dSl`/`hSl`/`pSl`/`nSl`, `lkB`, `hdl`, `Pub7`, `Dn7`, `ctx7`.
- `OwnAE4Lock.lean` (527) — `resplit7`, `hclaim7`, `dM_alloc`/`dM_tok`, slot deposits/claims, `dead7`,
  `l2_byte7`, `chain7`, `claim7`, `acq7`.
- `OwnAE4Gen.lean` (761) — `fI`, `wsM`, `QE7`, `waitG`, `loopG`, `cpu1G`, `relG`, `roundG`, `wpKA_fupd`.
- `OwnAE4H1.lean` (482) — `RKa`, `csA` (critical section), `acqR` (an acquirer's rounds).
- `OwnAE4H0.lean` (603) — `RK0`, `prt_birth`, `h0A` (kfree/initlock/publication), `done_claim`, `h0R` (rounds).
- `OwnAE4.lean` (373) — `setup7`, `premise7`, THE VERDICT `own_e4`.
