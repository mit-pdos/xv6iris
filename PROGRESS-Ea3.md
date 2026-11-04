# E-a3 progress — the TENURE-DEPENDENT RACY READ on track (a), dead set empty

Brief: ~/dev/weak-orch/promising/Ea3_prompt.txt (owner ruling [OWN.P13], context.md item 20; G4-review2.md §1
note 1, §6 A-1′, §8 item 8).  PASS = G4 (3) re-proved where hart 1 first acquires (xv6 text), writes its cpu into
the lock's cpu field, releases (xv6 text), then runs `holding()` + acquire's panic test, while hart 0 also
acquires/releases; verdict: hart 1 never panics; `Dd := fun _ => False`, 0 named inputs, ≤ 2k new lines (hard
stop 3k).  New files only: OwnAE3*.lean.

## Status (top): DONE — PASS (2026-11-04).  Proved, dead set empty, 0 named inputs, 936 new lines
- THE VERDICT `own_e3` (Weak/Prom/OwnAE3.lean): `∀ M run, validRun (xStep xs6) imgL () (progs t6) M run →
  ∀ h, noF (run.trace h)` — NO hart panics; `own_e3_h1` = the brief's statement (`noF (run.trace 1)`).
- Through `adequacyA` at `Dd := fun _ => False`, protocol `π6`; `#print axioms own_e3` / `own_e3_h1`:
  propext, Classical.choice, Quot.sound.  No free mode, no deadInv, no dead set.
- Build: `lake build Weak.Prom.OwnAE3` green (277 jobs), no warnings in the new files.
- New files only (namespace `Weak.Prom.OA.E3`); no existing file touched; no root edit.
- Lines: OwnAE3Defs.lean 325 (text, protocol, classes, pure racy read, coherence, bags, setup), OwnAE3.lean 611
  (tails, spin loop, hart, premise, verdict).

## The test (`t6`)
Both harts run the SAME xv6 text: acquire (spin loop `mv; amoswap.w.aq; sext.w; bnez`), `sd a0,16(s1)` (its
cpu in the field: its TENURE), release (`sd zero,16(s1); fence rw,w; sw zero,0(s1)`), then the next acquire's
`holding()` panic test (`lw; beqz; ld 16(s1); sub; seqz; beqz; sd a0,0(a2)`).  Stronger than the brief (hart 0 also
runs the test; the verdict is for every hart); mutual exclusion is not needed for the verdict and not proved.

## The protocol and the ownership argument
- `π6` (AUTHOR-AWARE, TIMESTAMP-BLIND, M-blind): a message touching the cpu field is an 8-byte message at it,
  by a hart `h < 2`, holding `0` or `cpuOf h`.  No tenure in it; each fulfil proves it outright.
- Per-AUTHOR owners from boot (`setup6`): hart `h` holds the `pend` of every message it authors that touches
  the field (`lbB (isP6 M h)`, any shape/content), its AMOs (`lbB (shp (mA6 h))`, lower-bounded by its coherence
  floor at `Lk`, consumed by the loop), its release words, its markers.  The rest stays with the boot owner, unused.
- At the racy `ld a5,16(s1)` (`pc_read6` + `loadOk_cohP`): the own `sd zero` at `t2` raised the field's 8
  coherence floors to `t2` and every later step keeps them (`cohP`, backward chain `cohP_*`), so each byte's
  source is `t2` (value 0) or above (`src_ge_lw`) — the own `sd a0` (`t1 < t2`) is excluded by COHERENCE.
  A source above `t2` authored by `h` is in `h`'s own bag (it took only `t1`, `t2` out): `h` DOOMS with its
  `pend` (plan R-a1; the owner dooms, keeps every other resource; the marker bag still fulfils the rest).
  A source by the other hart meets `π6` under the core's guard `⟦t⟧` (`grd_self`): 0 or the other cpu.
  Hence `⟦|M|⟧ (value = 0 ∨ value = cpuOf (1 - h))`; `sub; seqz; beqz` skips the panic.

## Findings / S5 consequences
- A-1′ does NOT kill: no timestamp-aware protocol language and no program-specific fact were needed.  The
  tenure-dependent read = author-aware protocol + coherence over the reader's own last write + own-bag doom.
- The doom consumes the `pend` of an own FUTURE message; at S5 a hart that later writes the field again needs
  that `pend` never to be required: true because a fulfil at `ts` needs `coh < ts` and the read raised `coh`
  above the doomed message (pure; must be carried as a coherence fact, as here).
- The 2-hart value argument used that `cpuOf 0`/`cpuOf 1` differ in ONE byte (bytes may come from different
  messages).  With NCPU real `&cpus[i]` pointers bytes from several harts could in principle assemble `&cpus[h]`;
  S5 needs the generic single-copy-atomicity lemma "an aligned 8-byte load of a field whose protocol makes every
  message an aligned 8-byte message returns ONE message's data (under the guard)" — loadOk's common read point
  (M9) gives it; not built here (estimate 0.1–0.2k, program-agnostic).
- Per-AUTHOR bags for a field are a new boot family (one per hart per protected field), like E-a2's `ak`.
- Inherited, not addressed: lock death/reuse (E-a2 (iii)), `kfree` junk in the field (needs that story).

## Files (Weak/Prom/, namespace `OA.E3`)
- `OwnAE3Defs.lean` (325) — `p6`/`t6`/`cpuOf`, `π6` + `ok6_*`, classes `mA6`/`mR6`/`mF6`/`isP6`/`byA`,
  `pc_byte6`, `pc_read6` (THE RACY READ, pure), `cohP`, `loadOk_cohP`, `lbB`/`lbB_take`, `bags`, `split_h`,
  `setup6`.
- `OwnAE3.lean` (611) — `regs6`, `st_nonF6`, `cohP_*`, `h_end6`, `h_bad6`, `h_rel6` (tenure, release, holding,
  the doom), `loop6` (Löb), `hart6`, `premise6`, THE VERDICT `own_e3`, `own_e3_h1`.
