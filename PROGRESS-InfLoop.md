# PROGRESS — InfLoop (the end-to-end infinite-execution theorem for `tLoop`)

Owner request 2026-11-13 (verbatim): "write the end-to-end infinite-execution theorem for tLoop".  Worker: Opus,
workspace pcsl8.  Files (new only): `Weak/Prom/InfLoop*.lean` (namespace `Weak.Prom.InfLoop`).  No root edits, no
edits to existing files.

## Status

**GREEN — PASS (2026-11-13).**  `lake build Weak.Prom.InfLoop` succeeds (via lean-gcp), no warnings in the new
files; 1278 new lines in 5 new files; no existing file edited, no root edit.
* `inf_mpLoop` (Weak/Prom/InfLoop.lean:172) — stated EXACTLY as in the brief (only premise `infExec tLoop E` plus
  the event premises).  `#print axioms` = `[propext, Classical.choice, Quot.sound]`; 0 named inputs.  The scope
  facts are discharged inside: `tLoop_S3a : progS3aB tLoop = true` (decide, InfLoopRef.lean:39) and
  `singleSizeI_loop` (InfLoopRef.lean:359, from the program by induction over `E.st` via `conforms`).
* `inf_mpLoop_core` (InfLoop.lean:91) — a provably-sharper form: the flag premise is the VALUE `bytesVal rdat = 1`
  (implied by `rdat = [1,0,0,0]`); conclusion `rdat = [1,0,0,0]` for the data load.
* `inf_mpLoop_val` (InfLoop.lean:181) — the value form: flag value 1 → data value 1 (`bytesVal`).
* `O = [(1, j)]` is chosen inside the proof; the machine, the unrolling and the bridge appear only inside.

### Parts (lines)

| part | file | lines | key results |
|---|---|---|---|
| 1 path-exposing completeness | InfLoopCmp.lean | 167 | `unroll_runP` :30, `rvwmo_inf_completeP` :64 |
| 2 reference facts of `tLoop` | InfLoopRef.lean | 406 | `inv0_all`/`inv1_all`, `pc_pat` :297, `memFacts`, `singleSizeI_loop` :359, `noLoad0`, `par1` :390 |
| 3 the bridge | InfLoopBridge.lean | 307 | `sr_step` :99, `cr_step` :238, `cr_steps` :259, `bridge` :279 |
| 4 machine alternation | InfLoopMach.lean | 204 | `minv_step` :96, `alt_run` :162, `machRow_at` :186 |
| 5 assembly | InfLoop.lean | 194 | `inf_mpLoop_core` :91, `inf_mpLoop` :172, `inf_mpLoop_val` :181 |

### Route (as suggested, one addition)

1. `rvwmo_inf_completeP` = `rvwmo_inf_complete` (PfxUnroll.lean, not edited; its proof re-run from the exported
   lemmas `nonhalted_prefix`, `unroll_sym`, `runFrom_ok`, `rvwmoRef_XC`, `condsOk_C`, `singleSize_XC`, `agree_C`,
   `row_prefix`, `rvwmo_complete`) plus the conjunct `∀ h < |harts|, T'.prog h = unrP E h (K h) ∧ ∀ j < K h,
   (E.st h j).pc ≠ |T.prog h|`.  The agreement used is the existing `machRow` prefix only.
2. THE BRIDGE IS TLOOP-SPECIFIC (not generic): hypothesis `UOk` (the `j`-th unrolled instruction is `unr j` of
   `tLoop`'s instruction at `j % 4`), discharged from `pc_pat` (`pc = j % 4` before halting: the not-taken side of
   `beq zero,zero,0` halts, so a non-halted path always takes it).  Simulation `SR`: same registers, same queued
   labels, same `PState`/promises/log, loop `pc` = unrolled `pc % 4`; the loop machine's `beq zero,zero,0` is
   always taken (`brEval .eq 0 0`) → `0 = (j+1) % 4`, the unrolled one goes to `j+1` either way; same labels.
   The bridged run has the SAME event list, hence the same traces.  `lit_mpLoop` applies to it.
3. Back to `E`: `E`'s row through `j` is `(loads before i) ++ [i, j]` (`filt_two`, from `hnext`); `m` = number of
   loads before `i` is even (`par1`: hart 1's load is at `Y` iff an even number of loads precede it — from the
   program).  ADDITION (part 4): on the machine side `qLoop` speaks about adjacent memory entries and their
   ADDRESSES, which `machRow` forgets; `alt_run` (pure front-end invariant over `soloSteps`, as `loop_noDone`)
   shows hart 1's `k`-th memory entry is a 4-byte load at `Y`/`X` by parity of `k`, so `machRow_at` gives entry
   `m` (flag, value 1) and entry `m+1` (data); `qLoop` at `m` gives value 1; 4 bytes < 256 with value 1 are
   `[1,0,0,0]`.

## RVWMO first

`inf_mpLoop` speaks about EVERY execution of `tLoop` — finite or infinite — that the RVWMO axioms of the manual
allow: `infExec tLoop E` (PfxDefs.lean) is "the harts run the program (loops allowed, any number of iterations, the
branch outcomes existential per step), the path conditions hold, and `rvwmoRefInf` holds" — rvwmo.adoc's global
memory order as a strict total order of exactly the memory operations, preserved program order rules 1–13, the
load value axiom, the atomicity axiom, the §zalrsc conditions and the PROGRESS AXIOM read literally (no memory
operation preceded by infinitely many).  The conclusion is the manual's MP+fence.w.w+fence.r.r verdict PER
ITERATION: on hart 1, a data load that is the next memory operation after a flag load that returned 1 returns 1.
The only modelling inputs are the reference (Ref.lean, RefProg.lean, PfxDefs.lean `rvwmoRefInf`) — FAITHFUL.  The
machine, the unrolling and the observed set `O` appear only inside the proof.
