# Repair progress — post-rebase repair onto MachFix (stage tag `[rebase-repair]`)

Brief: ~/dev/weak-orch/promising/Repair_prompt.txt.  Workspace: xv6iris-pcsl4.

## Status (top): DONE, GREEN (2026-11-04)
- `lake build` of every Weak/Prom module (166 pre-existing + new `RepairCheck`) green.  No sorry / axiom /
  native_decide / opaque / implemented_by.
- No G4 verdict statement changed.  The only signature changes follow MachFix's pattern: per-test hart lemmas and
  kit load/AMO rules gain the auto-param `hnoinv` (no invalidate message in `M`, `:= by assumption`), discharged at
  the top theorem by `x_noInvalT hrun` (track (a)); track (b)'s Pre copies of NF_R / `ownAdequacy` DROP `invalFree`.
- `invalFree` kept (as the litmus fact "no CMO message", MachFix's finding) only where it feeds `loadOk_byte`:
  OwnLock1b `hC/hB/hA1/hA`, OwnLock1c `hE1…hStart`, OwnLock4 `g1*` (unchanged; it also fills `hnoinv` by
  `assumption`, `invalFree` unfolds to the same proposition).

## Edits (all marked `[rebase-repair]`)
- NfrPre.lean: `runSeg`, `runAll`, `schedule`, `nfR` lose `invalFree`; `memStep_restrict` gets MachFix's `hvr`
  arguments (as NfrRun.lean); final `wIfr` case uses `loadRunV` / `loadRunV_keep`; header updated.
- OwnWpPre.lean: `ownAdequacy` loses `invalFree` (`nfR hv hfb`); header/docstring updated.
- OwnKitPre.lean: `hstepO_rmw`, `hstepO_load`, `wpT_ld`, `wpT_amo` gain `hnoinv` (copy of OwnKit.lean's MachFix edit,
  incl. `noInval_take`).
- OwnKitX.lean: `wpT_ld`, `wpT_amo` gain `hnoinv`.
- OwnLock1b.lean: `hF`, `hF0`, `hE`, `hD` gain `hnoinv`; `g4_lock1b`'s `ownAdequacy` call drops `hinv`.
- OwnLock1c.lean, OwnLock4.lean: `g4_lock1c` / `g4_lockBirth` `ownAdequacy` call drops `hinv`.
- OwnALock1cFree.lean `lk_free1c`; OwnALock1cCS.lean `lk_cs1c`, `lk_cpu1`; OwnALock1c.lean `lk_loop1c`, `lk_hart1c`,
  `lk_premise1c` gain `hnoinv`; `own_lock1c`: `have hnoinv := x_noInvalT hrun`.
- OwnAHold.lean `h0_run`, `h1_run`, `premise3` gain `hnoinv`; `own_hold`: `have hnoinv := x_noInvalT hrun`.
- OwnAPipeFree `p4h_free`, OwnAPipeCS `h1_cld`, OwnAPipeH1 `h1_loop2`, OwnAPipeH1b `h1_loop1`, `h1_hart`, OwnAPipe
  `p_premise` gain `hnoinv`; `own_pipe`: `have hnoinv := x_noInvalT hrun`.
- NEW Weak/Prom/RepairCheck.lean: `#print axioms` of the 15 G4 verdicts.

## Axioms (RepairCheck.lean) — all `[propext, Classical.choice, Quot.sound]`
Track (a): own_mp, own_mp2, own_lock1a, own_lock1b, own_lock1c, own_hold, own_pipe, slot_two_readers.
Track (b): g4_mpOwnL, g4_mp2, g4_lock, g4_lock1b, g4_lock1c, g4_lockBirth, g4_noDoubleClaimL.
