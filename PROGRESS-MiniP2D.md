# PROGRESS — mini P2-D (L4 MiniCmp completeness + L5 MiniPfx prefix lemma), workspace pcsl12

Brief: ~/dev/weak-orch/promising/mini/P2D_prompt.txt; plan rev 4 §2 L4/L5; P1gate-review.md §5.

## STATUS: DONE, ALL GREEN (2026-11-17). No kill fired (L4 2127 ≤ 3.5k; L5 1687 ≤ 1.8k; total 3822 ≤ 6k).

`lake build Weak.Mini.CmpCheck` (closure = all Cmp*/Pfx* files) green, 0 warnings in my files. `#print axioms`
(CmpCheck.lean): mini_complete, mini_prefix, mini_inf_complete = [propext, Classical.choice, Quot.sound].
No sorry/axiom/native_decide/opaque/implemented_by. 0 named inputs. No root edits; no existing file edited.
Imports: only Weak.Mini.Ref, Weak.Mini.Mach and my own Cmp*/Pfx* files (no Weak.Prom, MachCSL, Weak.WeakMem).

## Theorems
- `Weak.Mini.mini_complete` — Weak/Mini/CmpMain.lean:256 (proof `Cmp.completeRun`, :182)
```
(P) (hwf : P.wf) (himm : P.immOk) (C) (hC : miniCut P C) :
  ∃ r, miniValidRun P (cutMem P C) r ∧ (∀ h, loadVals (r.trace h) = cutLoads P C h) ∧
    ∃ c, mSteps P (mInit P) r.evs c ∧ ∀ h < P.harts.length, ∃ H, c.hs[h]? = some H ∧
      H.fr.pc = (C.st P h).pc ∧ ∀ reg, H.fr.rd reg = ((C.st P h).rd reg).1
```
  Preserved: per-hart load values in program order; final memory = the cut's stores in gmo order; each hart's final
  pc and register values (the cut's path; the front end loops, the run executes P's own text).
- `Weak.Mini.mini_prefix` — Weak/Mini/PfxMain.lean:155
```
(P X) (hX : miniExec P X) (O) (hO : ∀ e ∈ O, (X.evs P).isMem e) :
  ∃ C, miniCut P C ∧ (∀ o ∈ O, ∀ i ≤ o.2, (C.evs P).has (o.1,i) ∧ (C.evs P).ev (o.1,i) = (X.evs P).ev (o.1,i)) ∧
    ∀ h < P.harts.length, (C.st P h).pc = (mrun P X.V h (C.ks h)).pc ∧ (C.st P h).ctl = (… ).ctl ∧
      (C.st P h).evs.map noV = (mrun P X.V h (C.ks h)).evs.map noV
```
- `Weak.Mini.mini_inf_complete` — Weak/Mini/PfxMain.lean:201 (proof `Pfx.infCompleteRun`, :172)
```
(P) (hwf) (himm) (X) (hX : miniExec P X) (O) (hO) :
  ∃ ks Mm r, miniValidRun P Mm r ∧ (∀ o ∈ O, rowX P X o.1 (o.2+1) <+: loadVals (r.trace o.1)) ∧
    ∃ c, mSteps P (mInit P) r.evs c ∧ ∀ h < P.harts.length, ∃ H, c.hs[h]? = some H ∧ H.fr.pc = (mrun P X.V h (ks h)).pc
```
  The path is exposed (`ks`, final pc = X's hart after `ks h` steps); the run's harts are `mInit P` (P's own texts),
  so no `unrollOf` gap (Weak/Prom/PfxUnroll.lean) arises.

## Cones (tools/cone/Cone.lean, `lake env lean --run tools/cone/Cone.lean Weak.Mini.PfxMain …`; no ALIEN)
- mini_complete: mini=648 (total 2736, 486 decls) = miniCut ∪ miniValidRun (both were ~319/359) + cutMem/memL/msgOf/
  cutLoads/ldVals/immOk (16) + statement. > 600 (K5 gate value) but < 900 (K2); NOT a §0 vetted statement.
- mini_prefix: mini=356 (2366, 383 decls) = miniExec/miniCut + noV + statement.
- mini_inf_complete: mini=640 (2763, 484 decls).

## Lines
L4 2127: CmpBase 397 (run facts, shared with L5), CmpVo 130, CmpHart 208, CmpInv 315, CmpRules 174, CmpStep 216,
CmpStepM 425, CmpMain 262 (+ CmpCheck 8).  L5 1687: PfxRank 196, PfxTaint 169, PfxCut 432, PfxVal 259, PfxFix 145,
PfxAx 277, PfxMain 209.

## FINDINGS
1. L4 needs `MProg.immOk` (CmpStep.lean: every `alui` immediate < 2^64). Ref.lean `exec` computes
   `op.eval v1 (imm % two64)`, Mach.lean `instrNext` `op.eval (rd rs1) imm` (= machine v2 / MachCert). They differ
   for `slt`/`sltu` with imm ≥ 2^64: `sltiu x1, x0, 2^64` gives ref 0, mach 1; a following `lw x2, 0(x1)` (sz 4) is
   aligned for the ref and misaligned (stuck) for the machine, so the ref's load observation has no machine run.
   `MProg.wf` does not bound immediates; the full S3a completeness has the same premise (`progS3aB`). Fix options:
   add `imm < 2^64` to `MProg.wf`, or make one side reduce `imm`.
2. The brief's "cut's states EQUAL to the execution's states" (and plan L5's "po-down + gmo-down closure") is not
   attainable in general: the po ∪ gmo-down (even po ∪ rf) closure of O can be INFINITE. Example: hart A loops
   `lw r1,x; addi r2,r2,1; sw r2,y`, hart B the same with x/y swapped; gmo places A's k-th load after B's 2k-th
   store (and symmetrically); RVWMO-valid (no ppo from a load to a later independent store; progress holds). With O =
   {A's first store}: A.ld1 reads B.st2 (value 2, written by no other store), so any value-preserving cut needs
   B.st2, hence B.ld2, which reads A.st4, … So, as Weak/Prom/PfxVal.lean does, the cut keeps every event of
   po-down(O) unchanged, keeps every hart's path (pc, control taint, events up to their values: `noV`), and
   RE-SOURCES the "late" loads (values fixed by iteration over gmo rank). `mini_prefix` states exactly that.

## Design (L4)
Pulte AtoP: promise every store of `C.g` in order (`promAll`; timestamp `vo` = number of stores of `C.g` up to the
event), then replay hart after hart (`run_hart`/`step_any`), invariant `Inv` (CmpInv.lean): PAST form
regv/vrOld/vwOld, FUTURE form vrNew (rule 4), vwNew (4), vcap (11, 13), coh1 (1), coh2 (1, 2 + LVA: `kts_corr`),
fwd (12), promises = future stores' timestamps.
## Design (L5)
PfxRank (progress → finite gmo-predecessors, rank), PfxTaint (`agree_run`: taints are sound), PfxCut (anchors
O ∪ stores of gmo-down(po-down(O) mem ops), `ksOf` = first step reaching the cut, `deps_G`), PfxVal/PfxFix
(re-sourced values `VC`, fixpoint), PfxAx (the cut's axioms; rules 2/12 via `rule2_X`/`rule12_X`), PfxMain.

## Log
- L4 green (CmpBase…CmpMain); L5 green (PfxRank…PfxMain); composition green; cones measured; proofs of the two long
  headlines moved to `Cmp.completeRun`/`Pfx.infCompleteRun` so the cone tool does not count proof lines.
