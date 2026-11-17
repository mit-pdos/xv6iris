# PROGRESS — MiniP2C (mini plan rev 4 §2 L3 MiniLogic + machine-level example lemmas)

Worker: Opus (P2-C). Workspace `/home/bsdinis/dev/xv6iris-pcsl11`. Brief: `~/dev/weak-orch/promising/mini/P2C_prompt.txt`.

## Status (top): DONE, GREEN — no kill criterion fired

- `lake build Weak.Mini.LogicCheck` green (224 jobs), 0 warnings in the new files.  `#print axioms` (LogicCheck.lean)
  of `mini_adequacy`, the nine leaf rules, `mini_lit_lbdd`, `mini_lit_mpFF`, `mini_lit_mpLoop`:
  `[propext, Classical.choice, Quot.sound]`.  No sorry/axiom/native_decide/opaque/implemented_by; 0 named inputs.
- Deliverables: `mini_adequacy` Weak/Mini/Adeq.lean:123; `mini_lit_lbdd` LitLbdd.lean:119; `mini_lit_mpFF`
  LitMpFF.lean:176; `mini_lit_mpLoop` LitLoop.lean:295; leaf rules Rules.lean:170–325 (wp_alui, wp_alu, wp_fence,
  wp_br (any target ≤ text length: backward), wp_jmp, wp_nop, wp_load, wp_store, wp_done); `wpH_lift` Logic.lean:130.
- Lines: L3 = Run 582 + Logic 192 + Adeq 170 + Rules 341 = 1285 (budget 1.8k); examples = LitBase 247 + LitLbdd 152
  + LitMpFF 240 + LitLoop 359 = 998 (budget 1.2k); LogicCheck 19.  Total 2302 (< 4k stop).
- Cones (tools/cone/Cone.lean, Weak.Mini lines, no ALIEN): `mini_adequacy` mini=482 (target ≤ 750): Mach 265,
  Logic 62, Prog 54, Adeq 51, Val 37, Run 13; non-Mini by name: Iris 546 decls (Algebra 316: OFE/CMRA/Agree/View/
  Auth/DFrac/COFESolver/IProp/UPred; Std 103: CoPset/PartialMap/GenSets/Positives; Instances 71: UPred, WSat,
  LaterCredits, IProp, FUpd, GhostVar; BI 34; ProgramLogic 22: `wp`/`wp.pre`, `IrisGS_gen`, `StateInterp`,
  `Language`/`PrimStep`/`ToVal`), Lean core Init 519, Std 218.  Lemmas (not vetted): `mini_lit_lbdd` mini=413,
  `mini_lit_mpFF` 448, `mini_lit_mpLoop` 462.
- Programs: `lbddP` (= EqRefWit `lbddM`, rfl by inspection), `mpFFP` (RefTests `mpFF`), `loopP` (CoreLitLoop `tLoop`);
  all in namespace `Weak.Mini.Logic`.
- Import discipline: new files import only Weak.Mini.{Val,Prog,Mach} (via Run/Logic/…) and Iris.*; no Weak.Prom,
  no MachCSL, no Weak.WeakMem.  No existing file edited; no root edits.

## Design (decided before code)
- Files (all NEW, under Weak/Mini/): `Run.lean` (machine facts: solo projection against the final log by
  log-extension monotonicity — no promises-first factorization needed; partition; trace wf), `Logic.lean` (hart
  language, state interpretation, `wp`, lifting lemma), `Adeq.lean` (`mini_adequacy`), `Rules.lean` (leaf rules),
  `LitLbdd.lean`, `LitMpFF.lean`, `LitLoop.lean`.
- Trivial protocol only (no `Proto`/`Valid`/guards): none of the three examples needs more.
- Imports: Weak.Mini.{Val,Prog,Mach} + Iris.* only.

## Log
- GREEN `Weak.Mini.Run` (machine facts: `mSteps_solo`, `mSteps_partition`, `solo_wf`), `Weak.Mini.Logic` (hart
  language, `hartSt`/`hartInterp`, `wpH`, `wp`, `wpH_lift`), `Weak.Mini.Adeq` (`mini_adequacy`, `hart_adequate`).
- Cone `Weak.Mini.Logic.mini_adequacy`: mini=482 (Mach 265, Logic 62, Prog 54, Adeq 51, Val 37, Run 13), decls=1401,
  no ALIEN (non-Mini: Init 519, Iris 546, Std 218 decls).
- GREEN `Weak.Mini.Rules` (leaf rules: wp_alui/alu/fence/br (any tgt ≤ n)/jmp/nop/load/store/done, from `wpH_lift`).
- GREEN `Weak.Mini.LitBase` (miniGF, memEv, `adeqMem`, view facts, `read_src`), `Weak.Mini.LitLbdd`
  (`mini_lit_lbdd`), `Weak.Mini.LitMpFF` (`mini_lit_mpFF`).
- GREEN `Weak.Mini.LitLoop` (`mini_lit_mpLoop`, Löb at both loop heads, backward `beq` via `wp_br`), `LogicCheck`.

## Notes for the coordinator
- `mini_adequacy` statement: over `mSteps P (mInit P) evs c` + `noProm c`; Ψ/Φ chosen after the run (wp premise
  against `c.log`, for every hart slot of `mInit P`); exports (ii) Ψ at every prefix, (i) Φ of finished harts
  (`mDone`: nothing queued, no instruction at pc), (iii) `t ∈ fulfilsOf h evs ↔ 0 < t ∧ ownAt c.log h t` and Nodup,
  (v) `entryWf` of every entry.  Trivial protocol only; no example needed more.
- Proof route differs from the full stack: no promises-first factorization; the solo projection uses that a state
  step's admissibility reads the log only below the hart's views (`vle`), and logs only grow (`mMem_ext`).
- The logic does not track promise sets (`hstep` takes any `pr pr'`); the partition is a machine invariant
  (`PInv`, Run.lean).
