# PROGRESS — S3d (the prefix lemma, NA-1; plan rev 7 §6 S3d, §8 S3d, §9 Q1; [OWN.P4])

Worker: Opus (S3d). Workspace `/home/bsdinis/dev/xv6iris-pcsl2`.

## Status (top): GREEN; prefix lemma PROVED for the S3a scope; no kill criterion fired
- `rvwmo_prefix` PROVED (Weak/Prom/PfxMain.lean); `rvwmo_inf_complete` (composition with `rvwmo_complete`)
  PROVED (Weak/Prom/PfxUnroll.lean). `#print axioms` (PfxAxioms.lean): propext, Classical.choice, Quot.sound, both.
- K3d (counterexample): NOT fired — no counterexample; the lemma is true in the S3a scope (proof below).
- K3 (program-specific premise): NOT fired — premises are the scope Bool `progS3aB`, the execution (`infExec`),
  and for the composition NA-6 `singleSizeI` (as `rvwmo_complete` takes `singleSize`).
- Size: 2.7k lines, 9 NEW files (Pfx*.lean); no existing file edited.
- Build: `lake build Weak.Prom.PfxAxioms` green (closure = all Pfx files + CmpMain). `tools/ci/lint.sh` not run.

## Statements
```
-- PfxDefs.lean: infinite executions (literal transcription of Ref.lean's axioms over a gmo RELATION + progress)
def infExec (T : Test) (E : IExec) : Prop := E.T = T ∧ E.conforms ∧ E.condsOkI ∧ E.rvwmoRefInf
def partExec (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) : Prop :=
  trs.length = T.harts.length ∧ (∀ h (hh : h < trs.length), LReach (T.prog h) h (T.init h) trs[h]) ∧
    condsOk ν trs = true ∧ rvwmoRef (conc T trs ν g)

-- PfxMain.lean
theorem rvwmo_prefix {T : Test} (hT : progS3aB T = true) {E : IExec} (hE : infExec T E) (O : List EvId)
    (hO : ∀ e ∈ O, E.isMem e) :
    ∃ trs ν g, partExec T trs ν g ∧
      ∀ o ∈ O, ∀ i ≤ o.2, (o.1, i) ∈ (conc T trs ν g).ids ∧ (conc T trs ν g).ev (o.1, i) = E.ev (o.1, i)

-- PfxUnroll.lean
theorem rvwmo_inf_complete {T} (hT : progS3aB T = true) {E} (hE : infExec T E) (hss : singleSizeI E) (O)
    (hO : ∀ e ∈ O, E.isMem e) :
    ∃ T' chs trs ν g, unrollOf T T' ∧ T'.runAll chs = some trs ∧ condsOk ν trs = true ∧ rvwmoRef (conc T' trs ν g) ∧
      (∀ o ∈ O, ∀ i ≤ o.2, … (conc T' trs ν g).ev (o.1, i) = E.ev (o.1, i)) ∧
      ∃ run, PF.validRun litStep (testImg T') () (progs T') (memOf …) run ∧ promisesFirst run.evs ∧ allDone run.cfg ∧
        ∀ o ∈ O, (E's load row of hart o.1 up to o) <+: machRow (run.trace o.1)
```
- Reference side: `stepL` = RefProg's `stepI` with branches/jumps to ANY target ≤ |prog| (the loop front end; machine
  side OwnAFront `xNext`); a hart's run = states `st h k`, each an `LStep` (halted = stays); events = the states'
  events. `rvwmoRefInf`: gmo strict total order of the memory operations, `rfI` = the gmo-latest candidate (or the
  image), rules 1–13, I/O orders, LVA, atomicity, §zalrsc, PROGRESS literally (no injective predecessor sequence).
- Observations: every event of every hart up to an observed one is IDENTICAL (skeleton, address, bytes read and
  written) in the finite partial execution.

## Proof (formalised as stated)
O finite memory operations. P = po-down(O), M = its memory operations, G (`Gl`) = gmo-down-closure of M — FINITE
(`preds_finite`: progress ⇒ finitely many gmo-predecessors; `rk` = their number, `gmo ↔ rk <`). Anchors = O ∪
stores of G; the cut D = each hart up to its last anchor (a po-prefix; finite). gmo' = gmo|D (`gC`).
- `deps_G` (THE KEY BOUND): every address/control dependency of an event of D is in G — below an O-anchor it is in
  P; below a store anchor z it is ordered before z by rule 11 (z's control deps contain every earlier event's),
  rule 9 (z's address) or rule 13 (an address dep of an earlier memory op). So every address and every path
  condition of D only mentions loads of G.
- Loads of D ∩ G keep their value (`νC_kv`, induction on rank): the source is in D (gmo-below ⇒ an anchor store;
  po-below ⇒ in D) and its data deps are gmo-earlier loads of G (rule 10, or rule 12 if forwarded).
- Other ("late") loads of D are re-sourced: value = bytes of the gmo-latest candidate IN D, a fixpoint along gmo
  (`νC_fix`; a source's data only depends on gmo-earlier loads: rule 10/12, `dep_src`).
- ppo of the cut ⊆ gmo (`ppoAx_XC`): rule 1 + static rules are E's (same skeletons/addresses; po-between events are
  in D); rules 2 and 12 by a candidate-set argument against E's LVA and E's rules 2/12 (`rule2_XC`, `rule12_XC`).
- Why no counterexample: the naive closure (keep every value of po-down) can be infinite (LB-like chain); a
  changed-address store that would corrupt a kept load needs an infinite gmo-descending chain — rule 13 forbids it
  under progress. The plan's worry (chains through rf ∘ po) is bounded because every influence on a STORE is
  gmo-before it (rules 9–11, 13) and kept loads are gmo-bounded by M.

## Scope and open items
- Scope: `progS3aB` (no I/O; ALU, plain loads/stores of ANY sizes — mixed-size allowed in `rvwmo_prefix`, NA-6 only
  in the composition; FENCE, FENCE.TSO; loops; csrr; fence.i; nop). NOT covered: AMO, LR/SC, aq/rl (S3b scope),
  `addiw` (OwnAFront's XI; xv6's `sext.w` — not an `Instr`), I/O, translation. The proof route extends to AMO/LR/SC
  (rule 3: a cut source gmo-after the load would be E's forwarded source; atomicity/§zalrsc: stores of the cut ⊆ E's)
  — not formalised.
- Composition gap (machine side): `rvwmo_inf_complete` gives a machine-v2 run of the UNROLLED loop-free test `T'`
  (litStep), not of the looping program on the loop front end (`xStep`, which the S4 targets use). Remaining bridge
  (machine-level, no reference content): a litStep run of `unrP` is an xStep run of the loop program with the same
  labels (same instruction texts, same `LCtrl`/`LInstr` branch labels; only `pc` differs; needs the branch outcome
  on concrete registers = the path condition, i.e. registers = symbolic eval).

## Files (Weak/Prom/, all NEW)
PfxDefs (definitions, statement vocabulary), PfxSym (loop front end invariants), PfxRank (progress ⇒ ranking),
PfxCut (cut, `deps_G`), PfxVal (gmo', re-sourced values, LVA), PfxPpo (ppo), PfxMain (`rvwmo_prefix`), PfxUnroll
(`rvwmo_inf_complete`), PfxAxioms (`#print axioms`).
