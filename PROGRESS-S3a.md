# PROGRESS — S3a (completeness, single-size; plan rev 7 §6, §8 S3a)

Worker: Opus (S3a). Workspace `/home/bsdinis/dev/xv6iris-pcsl2`.

## Status (top): GREEN, DONE; no kill criterion fired
- `rvwmo_complete` PROVED (Weak/Prom/CmpMain.lean). `#print axioms`: propext, Classical.choice, Quot.sound.
- K3 (program-specific premise): NOT fired — the premises are the S3a scope Bool `progS3aB`, the execution
  (`runAll`, `condsOk`, `rvwmoRef`), NA-6 `singleSize`, `platformOrd` (= True with translation off).
- K3a (> 30k lines): NOT fired — 5.3k lines in 16 new files.
- Acceptance: all 21 FORBIDDEN rows of plan §5 in S3a's scope re-derived as ref ⇒ mach ⇒ lit (CmpLitT.lean),
  each checked against `Ref*.lean`'s `ref_<row>` by an `rfl` between proofs of the same statement.
- Build: `lake build Weak.Prom.CmpLitT` green (closure = all Cmp files); lint: only the expected drift findings
  (Weak/Prom files are not imported from the roots, by design).

## Statement (CmpMain.lean)
```
theorem rvwmo_complete (T : Test) (hT : progS3aB T = true) (hrun : T.runAll chs = some trs)
    (hc : condsOk ν trs = true) (hX : rvwmoRef (conc T trs ν g)) (hss : singleSize (conc T trs ν g))
    (_ : platformOrd (conc T trs ν g)) :
    ∃ run : PF.PFRun LP Unit,
      PF.validRun litStep (testImg T) () (progs T) (memOf (conc T trs ν g)) run ∧ promisesFirst run.evs ∧
      run.cfg.pcAgs.length = T.harts.length ∧ allDone run.cfg ∧
      (∀ h, machRow (run.trace h) = refRow (conc T trs ν g) h) ∧
      (∀ h r, regOf run.cfg h r = finalReg trs ν h r) ∧
      (∀ a n, finalMem (testImg T) (memOf (conc T trs ν g)) a n = refFinalMem (conc T trs ν g) a n)
```
`memOf X` = the stores of gmo in order (plan §6 "M := writes in gmo order"); `machRow`/`refRow` = every load's
answered bytes per hart in program order (so `run.obsLoad = refObsLoad`, `obsLoad_eq`). `rvwmo_complete_exec`: the
same from RefProg's `progExec T chs ν g`.

Scope (`progS3aB`, CmpDefs.lean): no I/O; ALU, plain `l*`/`s*` of 1/2/4/8 bytes, FENCE, FENCE.TSO, branches, jumps,
`csrr`, `fence.i`, `nop`; registers < 32, immediates < 2^64; image bytes < 256. NA-6 (`singleSize`, plan §9 NA-6
"every byte is always accessed at one width and alignment"): two memory operations touching a common byte have the
same address and size. For uniform-size programs NA-6 holds of every execution (`singleSize_of_uniform`, CmpLit).

## Proof structure (Pulte AtoP.v, plan §6)
- Run = promise every message of `memOf X` in log order (MachFactor `promsRun`), then each hart's reference path to
  completion, hart after hart (`statePhase`, `solo_lift`).
- Per hart: `SimInv` (CmpInv.lean) relates the symbolic state to (program state, PState, promises). Views are
  bounded by `vo X e` (Pulte `view_of_eid`): PAST form (`domF` = `sim_view`) for registers, vrOld, vwOld;
  FUTURE form for vrNew (rule 4), vwNew (rule 4), vcap (rules 11, 13), coh (rule 1: `coh1`; rules 1, 2 + LVA:
  `coh2`), forward bank (`fwdOk`, rule 12); promises = future stores' timestamps.
- Steps: CmpSimN (ALU, csrr, jmp, nop, fence.i, br), CmpSimF (FENCE, FENCE.TSO), CmpSimL/Ld (load: `loadOk_ref`,
  `load_pre_le`, `fwdView_le_vo`, `kts_lt_store`), CmpSimS (store: COH by `coh1`, EXT by rules 9, 10 + invariant).
- Reference facts (CmpRef): `gB_of_ppo`, `rfSrc_max`, ppo constructors (rules 1, 2, 4, 9–13), `corr`, `srcFwd`,
  `rfSrc_bytes` (the one use of NA-6, plus `uniTvs`: one timestamp per load).

## Acceptance (CmpLitT.lean)
Generic: `refFromLit` (rvwmo_complete + a `lit_` property of every valid run ⇒ the same property of every
reference execution's observations); `forbid_of_lit` (+ a dataflow bridge `regLoadB`, decided over all paths, ⇒
`forbiddenRef T`, the statement of `ref_<row>`).
- `refLit_<row> : forbiddenRef <row>` with `refLit_<row>_agrees : refLit_<row> = Lit.ref_<row> := rfl` — 17 rows:
  lbdd, lbDatas, lbCtrls, oota42, mpFF, mpFFrr, mpFAddr, sbFF, datarfi, addrpo, w22F, isa2F, wrcF, iriwF, coWW,
  coWR, coRR2.
- coWR0, coRW1, coRW2, coRR (their `lit_` theorems state the coherence-violating sub-outcome of the repository
  condition, CoreLitCo.lean header): `refFromLit_<row>` (from the logic) and `refChk_<row>` (the same statement
  from `ref_<row>`, the reference checker), `refFromLit_<row>_agrees := rfl`.

## Files (Weak/Prom/, all NEW; no existing file edited)
CmpDefs, CmpRef, CmpSym, CmpStep, CmpCtx, CmpInv, CmpSimN, CmpSimF, CmpSimL, CmpSimLd, CmpSimS, CmpSim, CmpRun,
CmpMain, CmpLit, CmpLitT.

## Open items for S3b (extension points)
- Invariant fields to add: `wVRel` (rule 7 RCsc), `wRes` (LR reservation: rule 8 via `rvView`, pair atomicity
  `exclOk`), `wRmw` (split AMO); aq/rl bounds on vrNew/vwNew (rule 5) and the release pre-view (rule 6) — Zalasr
  `loadAq`/`storeRl` also need them (excluded from `instrS3a` now).
- Forwarding from an AMO/SC: forward view = its own timestamp (M1) — the `fwdOk` bound then comes from rule 3.
- New step lemmas `sim_amo` (fused `LRmw`: read at `ldPre`, `exclOk` from the atomicity axiom on AMOs, M0 post),
  `sim_lr`, `sim_sc` (success: `exclOk` on the LR's bytes, `resvOk`; failure `LExFail`); `SymWf`/`Future` already
  cover all instructions; `stepI_stSz` / `instrS3a` to widen.
- `platformOrd` stays True until translation (OQ-1, [OWN.P3]).
- Not covered by S3a acceptance: rows 5, 10, 11, 11b, 23, 28, 28c, 37 (AMO / LR/SC: S3b); 32 (mixed-size: S3c);
  38 `lit_mpPtr` (stated over the faulting front end `litStepF`, not `litStep`); 4′ lbCtrlsBeq, 18r addrpoR (no
  `lit_` theorem yet).
- Mixed-size (S3c): NA-6 is used only in `rfSrc_bytes` and the uniform answer timestamp (`uniTvs`).
