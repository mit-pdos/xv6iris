# PROGRESS — mini P1fix (apply the P1 gate's fixes), workspace pcsl9

Brief: ~/dev/weak-orch/promising/mini/P1fix_prompt.txt; review ~/dev/weak-orch/promising/mini/P1gate-review.md.

## STATUS: DONE, ALL GREEN (2026-11-17)

`lake build Weak.Mini.EqRef Weak.Mini.EqRefCut Weak.Mini.EqRefLF Weak.Mini.EqRefWit Weak.Mini.EqMachCheck
Weak.Mini.MachLb Weak.Mini.Wf` green, 0 warnings in Weak/Mini. `#print axioms` (now all in EqMachCheck.lean): e1a, e1b,
e1aCut, e1bCut, e1aLF, e1bLF, mini_cut_witness, e2a, e2b, e2a_obsLoad, e2b_obsLoad, mini_lb_valid, writesIn_window =
[propext, Classical.choice, Quot.sound]; wf_progWf = [propext, Quot.sound]. No sorry/axiom/native_decide/opaque/
implemented_by. Nothing under Weak/Prom/ edited; no root edits. Import discipline: Val (none), Prog→Val, Ref→Prog,
Mach→Prog, Wf→Ref+Mach; only Eq*.lean import Weak.Prom.

Cones (tools/cone/Cone.lean, Weak.Mini lines; no ALIEN):
- `Weak.Mini.miniExec` mini=315 (Ref 224, Prog 54, Val 37), decls=365
- `Weak.Mini.miniCut` mini=319, decls=366
- `Weak.Mini.Mach.miniValidRun` mini=359 (Mach 268, Prog 54, Val 37), decls=379
- `Weak.Mini.MProg.wf` mini=73
(P1A/P1B numbers 401/405/556 were with the older tool and the duplicated value code.)

Statement changes: e2b (fix 1) — see below; `MProg.wf` (fix 4) strengthened; `Mach.loadOk` (fix 6) rewritten
(equivalent). No other theorem statement changed.

## Fixes (review's final numbering)
1. e2b: conclusion gains `run.evs = r.evs.map (embEv P)` (proof's `he`). e2b_obsLoad drops it.
2. New `Weak/Mini/Val.lean` (Lean core only): `MAlu`, `MBrC` (moved from Prog.lean), `two64`, `sltN`, `MAlu.eval`,
   `MBrC.eval`, `sext`. Prog.lean imports it. Ref.lean and Mach.lean copies deleted (Mach uses `op.eval`/`c.eval`).
3. Ref.lean citations name `promising/spec/unpriv_rv32.adoc`.
4. `MProg.wf` = RISC-V size (1/2/4/8) ∧ aligned image ∧ ∀ instr, tgtOk ∧ `MI.regOk` (rd/rs1/rs2 < 32).
   `MProg.wf.sz_pos` (Ref.lean). `MProg.wf_progWf` in new `Weak/Mini/Wf.lean`. `Mach.progWf` unchanged (E2 needs
   neither bound).
5. rule2 docstring: rf functional under gmoOk; `none` = initial memory as writer.
6. Mach `loadOk` = `memv … = some v ∧ ¬ writesIn log a t (max vpre (ws.coh a))`; `fwdHit` moved to EqMachMem as
   `fwdHitW`; `writesIn_window` (EqMachMem) is the equivalence with the old form.
7. Ref.lean header: one-store-per-word argument; MEv docstring: fence `pa`/`v` dummies.
8. rule13 mark as in the review table.

## Choices
- Fix 4 sizes: REQUIRED `sz ∈ {1,2,4,8}` in `MProg.wf` (every §1 example has sz 4 or 8; E1 only gets a stronger
  hypothesis, so stays true). Register bound in `wf` only; `Mach.progWf` unchanged (E2 holds without either).
- Fix 4 lemma placed in new Wf.lean (Ref and Mach do not import each other).
- EqMachCheck.lean also imports the E1 modules + Wf (one axiom-check file for the stage).
- Edited Eq files only for the renames: EqMachFront (`Mach.two64/aluOp/brEval` → `two64`/`op.eval`/`c.eval`),
  EqMach (`two64`, e2b), EqMachMem (`fwdHitW`, `writesIn_window`), EqRef (`tgtOk_of_wf`, `sz_pos`), EqRefWit (`lbddM_wf`).

## Log
- All fixes edited; Val/Prog/Ref/Mach/Wf/MachLb GREEN; all E1/E2 modules + EqMachCheck GREEN first try; axioms std;
  cones measured.
