# PROGRESS — mini P1-A (L1 MiniRef + E1), workspace pcsl9

Brief: ~/dev/weak-orch/promising/mini/P1A_prompt.txt; plan ~/dev/weak-orch/promising/mini/plan.md rev 4.

## STATUS: DONE, ALL GREEN (2026-11-17). E1 TRUE — K1 did not fire; no finding.

Std axioms only (`propext, Classical.choice, Quot.sound`) for e1a, e1b, e1aCut, e1bCut, e1aLF, e1bLF,
mini_cut_witness, corr_iff, refCore_cut (checked with `#print axioms` in a scratch module, since deleted).
No sorry/axiom/native_decide/opaque/implemented_by; 0 named inputs; no edits to existing files; no root edits.
Import discipline: Weak/Mini/Ref.lean imports only Weak.Mini.Prog; only Weak/Mini/EqRef*.lean import Weak.Prom.*.
Build: `lake build Weak.Mini.EqRefLF Weak.Mini.EqRefWit` (covers every new module), 0 warnings in Weak/Mini.

## Files (new, all under Weak/Mini/)
| file | lines | content |
|---|---|---|
| Ref.lean | 367 | L1 MiniRef: events, ONE axiom block `MEvs.ax`, concrete harts (`exec`, `mstep`, `mrun`), `miniExec`, `miniCut`, `MProg.wf`, `MProg.fwd`, `MCut.halted` |
| EqRefBase.lean | 610 | `MEv.toEv`, byte lemmas, image lemma, `Corr`, `corr_iff : Corr … → (E.rvwmoRefInf ↔ A.ax ini)` |
| EqRefSim.lean | 452 | `replay`/`rstep`/`chosen`, `SimSt`/`SimEv`, `sim_exec` (8 F arms), `sim_run`, `fstep_of_lstep`, `replay_sim` |
| EqRef.lean | 337 | `toFull`, `SimA` (`.corr`, `.bytes`), **e1a**, **e1b** |
| EqRefList.lean | 401 | `cutI`, `refCore_cut` (list `rvwmoRef (conc …)` ↔ relation `rvwmoRefInf` of the constant execution) |
| EqRefCut.lean | 360 | `toCut`, `reach_replay`, `replay_congr`, `SimC`, **e1aCut**, **e1bCut** |
| EqRefLF.lean | 294 | `symRun_reach`, `symRun_replay`, **e1aLF**, **e1bLF** |
| EqRefWit.lean | 42 | `lbddM`, `lbddCut`, **mini_cut_witness** (K4) |

Total 2863 (L1 367, E1 2496). Budget: L1 ≤ 0.7k OK; E1 ≤ 1.2k OVERRUN (core infinite pair ≈ 1.4k; the finite cut's
list↔relation bridge and the loop-free `symRun` corollary were not in the 0.8k estimate). Under the 3k stop.

## Declarations (file:line)
- MiniRef: `MEvs` Ref.lean:60; rules 1/2/4/9/10/11/12/13 at Ref.lean:98/103/118/122/126/129/133/140 (each with its
  rvwmo.adoc quote, FAITHFUL); `ppo` :147; `loadValueAx` :170; `ax` :181; `exec` :258; `mrun` :290;
  `miniExec` :320; `miniCut` :345; `MProg.wf` :357.  Rules 3, 5–8, atomicity, I/O vacuous on F (file header).
- E1a `e1a` EqRef.lean:275: `miniExec P X ↔ infExec (P.toTest cond) (toFull P cond X)` (`toFull` :61).
- E1b `e1b` EqRef.lean:303: `infExec (P.toTest cond) E → ∃ X, miniExec P X ∧ (∀ e, E.has e ↔ (toFull …).has e) ∧
  (∀ e, E.has e → E.ev e = (toFull …).ev e) ∧ E.gmo = (toFull …).gmo`.
- finite pair: `e1aCut` EqRefCut.lean:285 `miniCut P C ↔ partExec (P.toTest cond) (toCut P cond C) (nuOf P.sz C.V) C.g`;
  `e1bCut` :313 `partExec … trs ν g → ∃ C, miniCut P C ∧ trs = toCut P cond C ∧ ids-iff ∧ ev on ids ∧ g = C.g`
  (the [R4] conjunct, stated as LIST equality — stronger than per index).
- loop-free corollary: `e1aLF` EqRefLF.lean:235 (fwd program, halted cut → `progExec` along the recorded choices,
  `runAll = some (toCut …)`); `e1bLF` :261 (`progExec … chs ν g → ∃ C, miniCut ∧ halted ∧ runAll chs = some (toCut …)
  ∧ ids ∧ ev ∧ g = C.g`).
- K4 witness: `mini_cut_witness : ∃ C, miniCut lbddM C` EqRefWit.lean:36 (statement Mini-only; proof = kernel
  `decide` on the full `refCoreB` + `e1aCut`).

## Cones (tools/cone/Cone.lean, `lake env lean --run`, via lean-gcp)
- `Weak.Mini.miniExec`: mini=401 lines, 503 decls (total incl. core 2984), no ALIEN.
- `Weak.Mini.miniCut`: mini=405, 505 decls, no ALIEN.
- `Weak.Mini.MEvs.ax`: mini=148, 99 decls, no ALIEN.
- `Weak.Mini.MProg.wf`: mini=131 (Prog.lean types), no ALIEN.
(The tool counts an inductive's `.rec`/`.casesOn` with the inductive's own lines, so these over-count.)

## Choices to vet at the P1 gate (not discrepancies: E1 proves them equal to the full reference)
1. Scope `MProg.wf`: `0 < sz`, `sz`-aligned image, targets ≤ |text|.  Outside it the full front end is STUCK on an
   out-of-range target (no execution at all) while the mini hart would halt; excluded rather than modelled.
2. Registers outside 1…31 behave as `x0` (full: `SSt.rd` gives `.c 0`, `regs.set` past length 32 is a no-op).
3. A load's mini value is `V e mod 2^(8 sz)`, the initial word `img0 a mod 2^(8 sz)` (bytes cannot carry more;
   without the mod E1a would be false for `V e ≥ 2^(8 sz)`).
4. Event ids index loads/stores/fences exactly as `SSt.emit`; dependency lists built by `stepI`'s appends; fence
   events carry no dependencies (as `stepI`).
5. `miniCut` gives each hart a step count `ks h` (the hart semantics is deterministic, so this is `LReach`).

## Merge note (P1-B in pcsl10)
Helper names `two64`, `sltN`, `sext` exist in both `Weak.Mini` (mine) and `Weak.Mini.Mach` (P1-B); `aligned_eq`,
`aluOp_eq`, `brEval_eq`, `byteList_succ`, `bytesVal_byteList`, `two64_eq` exist in mine (`Weak.Mini`) and in P1-B's
`MiniEq` namespace.  Distinct full names (no clash on rebase), but duplicated definitions the coordinator may unify.

## Log
- Ref.lean GREEN; EqRefBase GREEN (`corr_iff`); EqRefSim GREEN; EqRef GREEN (e1a, e1b); EqRefList GREEN
  (`refCore_cut`); EqRefCut GREEN (e1aCut, e1bCut); EqRefWit GREEN (K4); EqRefLF GREEN (e1aLF, e1bLF); cones
  measured; warnings cleaned.
