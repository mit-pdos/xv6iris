# PROGRESS — MiniP1B (mini plan rev 4 §2 L2: MiniMach + E2)

Worker: Opus (P1-B). Workspace `/home/bsdinis/dev/xv6iris-pcsl10`. Brief: `~/dev/weak-orch/promising/mini/P1B_prompt.txt`.

## Status (top): DONE, GREEN — E2a/E2b PROVED; no kill criterion fired (K1 did not fire: no discrepancy beyond the known torn case)

- `lake build Weak.Mini.EqMachCheck` green (270 jobs). `#print axioms` of `MiniEq.e2a`, `MiniEq.e2b`,
  `MiniEq.e2a_obsLoad`, `MiniEq.e2b_obsLoad`, `Weak.Mini.Mach.mini_lb_valid`: `[propext, Classical.choice, Quot.sound]`.
  No sorry/axiom/native_decide/opaque/implemented_by. 0 named inputs.
- Import discipline: `Weak/Mini/Mach.lean` and `MachLb.lean` import only `Weak.Mini.Prog` / `Weak.Mini.Mach`;
  only `Weak/Mini/Eq*.lean` import `Weak.Prom.*`. Cone of `miniValidRun` has no ALIEN declaration.
- No existing file edited; nothing added to the `Weak` root (coordinator decides).

## Files (all NEW, under Weak/Mini/)
| file | lines | content |
|---|---|---|
| `Mach.lean` | 379 | L2 MiniMach (namespace `Weak.Mini.Mach`) |
| `MachLb.lean` | 76 | K4 witness `mini_lb_valid` |
| `EqMachBytes.lean` | 309 | word↔byte lemmas, `wordB`, `embMsg`, image/`memByte`/`writesIn` at a word |
| `EqMachFront.lean` | 525 | `embL`/`embF`, front-end equation `xNext_emb` (:230), image `xNext_image` (:334), `mNext_ok` |
| `EqMachMem.lean` | 441 | `RelWs` (:24, inertness invariant), `loadOk_iff` (:296), `mem_fwd` (:355), `mem_bwd` (:391) |
| `EqMach.lean` | 534 | `embEv/embTr/embM/embRun`, `untorn` (:51), `Rel`, step/run sims, `pass1` (:345), `e2a` (:454), `e2b` (:484), obsLoad corollaries (:522, :527) |
| `EqMachCheck.lean` | 11 | `#print axioms` |
L2 = 379 (budget 0.6k ✓). E2 = 1820 (budget 1.4k: OVER by ~0.4k). Total 2275 (< 3k stop).

## MiniMach (Weak/Mini/Mach.lean)
State `MSt` (:122): `coh`, `vrOld/vwOld/vrNew/vwNew`, `fwd` (per word, `Nat → Option (Nat × Nat)`), `regv`, `vcap`, `ldv`
— total functions; promises `List Nat`; messages `MMsg` (:97) `(pa, v, tid)`. Labels `MLab` (:81)
load/store/fence/regW/ctrl/instr. Memory half `mMem` (:206), one constructor per Machine.lean arm (each cites it,
all marked FAITHFUL); load rule `loadOk` (:171) carries the word form of the forwarding exemption (forwarded floor
`vpre ⊔ coh`, else `(vpre ⊔ t) ⊔ coh`, as Machine.lean:325–333). Looping front end `instrNext` (:265)/`mNext` (:297)
(branches/jumps any target ≤ n, as `xNext`). `mStep` (:326): promise + state; `miniValidRun` (:358).
Design notes:
- `mStep.promise` admits only aligned word messages (`pa % sz = 0`, `v < 2^(8 sz)`): per step STRONGER than
  Machine.lean's promise (any byte run), FAITHFUL on valid runs (only such messages can be fulfilled on F; E2a/E2b).
- `MRun` is the event list; the final configuration is the one the events reach (`mStep` deterministic, `mSteps_det`).
- ALU/branch/sext transliterated (Mach.lean §0; worker A's MiniRef needs the same — coordinator may dedupe).

## E2 (Weak/Mini/EqMach.lean, namespace `MiniEq`)
Hypothesis `Mach.progWf P` (Mach.lean:68): `0 < sz` and every image entry at an aligned address (Prog.lean's
"one value per sz-aligned word"; without it a misaligned image entry is read differently byte-wise).
- `e2a P hwf cond Mm r : miniValidRun P Mm r ↔ PF.validRun (xStep P.xs) (testImg (P.toTest cond)) () (progs (P.toTest
  cond)) (embM P Mm) (embRun P cond r)`. `embRun`'s configuration is `Classical.choose` of "the embedded events reach
  C" (noncomputable; E2a(→) shows it is the related one, via mini determinism).
- `e2b P hwf cond M run hv (hu : untorn run) : ∃ Mm r, M = embM P Mm ∧ miniValidRun P Mm r ∧ ∀ h, run.trace h =
  (r.trace h).map (embTr P)`; `untorn` verbatim from plan §2 L2.
- Inertness: `RelWs` keeps `wVRel = 0`, `wRes = wRmw = none`, `wIfl = wIfr = wIfv = 0`; every message plain (embedded);
  load `vi = 0` (`invalCite_vi0` + `noInval_emb`); labels only the six F labels (`xNext_image`).
- `wordB` maps an out-of-range value (never in a valid run) to a byte run of the wrong length, making the embedding
  injective; `pass1` shows every message of a full valid run is an aligned word (fulfilled by an F store).

## Cones (tools/cone/Cone.lean)
- `Weak.Mini.Mach.miniValidRun`: lines=3213, **mini=556**, decls=541, no ALIEN. De-duplicated by start line: 443
  (Mach 362 + Prog 81) — the tool counts an inductive's `rec`/`casesOn`/constructors again with the inductive's range.
- `Weak.Mini.Mach.mini_lb_valid`: mini=594 (dedup 473: Mach 376, MachLb 16, Prog 81), no ALIEN.
- Suggest adding `Weak.Mini.MachLb Weak.Mini.Mach.mini_lb_valid` to tools/ci/cone-targets.txt (not edited here).

## Findings
- None new. E2 holds exactly as planned; machine v2 ⊋ MiniMach only on torn runs (F3, MachTornWit.lean).
- Naming: Eq files use the top-level namespace `MiniEq` — inside `Weak.*`, WeakMem's `Weak.coh/regv/writesIn/…`
  clash with machine v2's names.

## Log
- 2026-11-17: `Weak.Mini.Mach` GREEN (L2 definitions; imports only `Weak.Mini.Prog`).
- 2026-11-17: `Weak.Mini.MachLb` GREEN (`mini_lb_valid`); `EqMachBytes`, `EqMachFront`, `EqMachMem` GREEN.
- 2026-11-17: `Weak.Mini.EqMach` GREEN (`e2a`, `e2b`, obsLoad corollaries); `EqMachCheck` axioms std; cones measured.
