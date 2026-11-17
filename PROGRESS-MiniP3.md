# PROGRESS — mini P3 (L6 headlines, witnesses, cross-check corollaries, cone manifests, reading guide), pcsl12

Brief: ~/dev/weak-orch/promising/mini/P3_prompt.txt; plan rev 4 §0, §2 L6, §4 K4/K5.

## STATUS: DONE, ALL GREEN (2026-11-17). No kill fired; cone gate K5 PASSES.

All 46 Weak/Mini modules build (one `lake build` of every module, 0 warnings in Weak/Mini).  `#print axioms`
(Weak/Mini/HeadCheck.lean): every headline, witness and corollary = [propext, Classical.choice, Quot.sound]
(`lbddP_eq`, `loopP_xs`: none; the `*_toTest` rfl's and `MProg.wf.immOk`: [propext]).  No sorry/axiom/native_decide/
opaque/implemented_by; 0 named inputs; no root edits; nothing outside Weak/Mini, notes/mini, tools/ci/cone-targets.txt.
New lines: Head 247, HeadAlt 272, HeadWit 88, EqHead 272, HeadCheck 26 = 905 (+ README 105).

### Deliverables (file:line)
- HEADLINES (Mini-only imports): `mini_forbidden_lbdd` Head.lean:82, `mini_forbidden_mpFF` :96, `mini_inf_mpLoop`
  :238 (one-line wrappers of `Head.forbiddenLbdd`/`Head.forbiddenMpFF`/`Head.infMpLoop`, so the cone tool counts
  statements only); `MCut.obsLoad` :33; `lbddP_wf`/`mpFFP_wf`/`loopP_wf` §2.
- WITNESSES (K4) HeadWit.lean: `mini_lbdd_witness` :36, `mini_mpFF_witness` :50, `mini_infExec_witness` :58,
  `mini_inf_mpLoop_exercised` :64, `mini_inf_mpLoop_exercised_concl` :79.
- CROSS-CHECKS EqHead.lean: `lbddP_eq` :29, `lbddP_toTest` :31, `mpFFP_toTest` :33, `loopP_toTest` :35, `loopP_xs`
  :37 (all rfl, i.e. the constants coincide); `ref_lbdd_mini` :116 / `ref_lbdd_of_mini : forbiddenRef Lit.lbdd` :151;
  `ref_mpFF_mini` :157 / `ref_mpFF_of_mini` :190; `transfer` (E1b event by event); `inf_mpLoop_of_mini` :244 (any
  cond); `inf_mpLoop_recovered` :263 (= InfLoop.lean `inf_mpLoop` statement verbatim).
- Helper HeadAlt.lean: `mini_alt_loop` (MiniMach: hart 1's memory entries alternate flag/data; Löb), `x_ok1`/
  `x_noLd0` (MiniRef closed form of loopP's harts).
- CONES (tools/ci/cone.sh on the VM, PASS; manifests notes/mini/cone/*.txt pulled back via tar|base64 through
  lean-gcp): lbdd 339, mpFF 344, mpLoop 339 (≤ 600), mini_adequacy 482 (≤ 750); no ALIEN.
- README notes/mini/README.md (105 lines).

### Statements changed by (0)
1. `MProg.wf` (Ref.lean:357): per-instruction conjunct `tgtOk ∧ regOk` → `tgtOk ∧ regOk ∧ immOk` (new `MI.immOk`
   :349).  Every theorem with a `P.wf` premise (e1a/e1b/e1aCut/e1bCut/e1aLF/e1bLF, mini_complete, …) keeps its text
   but now covers only programs with 64-bit ALU immediates.
2. `mini_complete` (CmpMain.lean:256): premise `(himm : P.immOk)` removed.
3. `mini_inf_complete` (PfxMain.lean:201): premise `(himm : P.immOk)` removed.
Internal `step_any`/`run_hart`/`Cmp.completeRun`/`Pfx.infCompleteRun` keep `himm` (fed by new `MProg.wf.immOk`,
CmpStep.lean:27).  One-line repairs: `.2` → `.2.1` at CmpStep.lean:108, CmpStepM.lean:44/:294, CmpMain.lean:66/:75;
`lbddM_wf` (EqRefWit.lean:31–32) proves the extra `trivial`; PfxMain.lean:179 call site.

### Note for the coordinator
- `mini_adequacy`'s cone (482) counts its 51-line declaration INCLUDING the proof (Adeq.lean:118–168); a one-line
  wrapper (as the headlines) would drop ~35 lines.  Not done: Adeq.lean is outside the allowed edit (0).
- Root imports for the new modules (Head, HeadAlt, HeadWit, EqHead, HeadCheck) are the coordinator's.

## Plan
- (0) fold `immOk` into `MProg.wf` (Ref.lean): new `MI.immOk`, per-instruction conjunct `tgtOk ∧ regOk ∧ immOk`;
  `MProg.wf.immOk` (CmpStep.lean); `mini_complete` / `mini_inf_complete` drop the `himm` premise.
- Head.lean (Mini-only): `MCut.obsLoad`, `mini_forbidden_lbdd`, `mini_forbidden_mpFF`, `mini_inf_mpLoop`.
- HeadAlt.lean: hart 1 of `loopP` alternates flag/data loads (machine: MiniLogic Löb; reference: closed form).
- HeadWit.lean (Eq imports allowed): finite witnesses for lbdd/mpFF, `mini_infExec_witness`, `mini_inf_mpLoop_exercised`.
- EqHead.lean: `ref_lbdd`/`ref_mpFF`/`inf_mpLoop`-shaped corollaries, constant equalities.
- cone-targets.txt + cone.sh on the VM; notes/mini/README.md.

## Log
- (0) GREEN: `MI.immOk` + `MProg.wf` 4th per-instruction conjunct (Ref.lean); `MProg.wf.immOk` (CmpStep.lean);
  `mini_complete`, `mini_inf_complete` lose `himm`; five `.2` → `.2.1` repairs (CmpStep/CmpStepM/CmpMain);
  `lbddM_wf` triple; CmpCheck/EqMachCheck/LogicCheck green, axioms std.
- HeadAlt.lean GREEN (`mini_alt_loop` machine alternation by Löb; `J1_all`/`x_ok1`/`x_noLd0` reference closed form).
- Head.lean GREEN: `mini_forbidden_lbdd`, `mini_forbidden_mpFF`, `mini_inf_mpLoop`.
- EqHead.lean GREEN; HeadWit.lean GREEN; HeadCheck axioms std; cone.sh PASS; README written; full Weak/Mini build green.
