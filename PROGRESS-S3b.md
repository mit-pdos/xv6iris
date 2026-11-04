# PROGRESS — S3b (completeness: AMOs, LR/SC, Zalasr; plan rev 7 §6, §8 S3b)

Worker: Opus (S3b). Workspace `/home/bsdinis/dev/xv6iris-pcsl2`.

## Status (top): GREEN, DONE; no kill criterion fired
- `rvwmo_complete` EXTENDED to S3b (Weak/Prom/CmpMain.lean), same promises-first form and exports
  (`rvwmo_complete`, `rvwmo_complete_exec`, `refFromLit`, `forbid_of_lit`, `obsLoad_eq`, `finalMem_eq`).
  `#print axioms` (CmpLitB.lean): propext, Classical.choice, Quot.sound — for the theorem and every row below.
- K3 (program-specific premise): NOT fired — premises are the Bool scope `progS3bB`, the execution (`runAll`,
  `condsOk`, `rvwmoRef`), NA-6 `singleSize`, `platformOrd` (= True, translation off).
- K3a-style size (> 2 × 8.5k): NOT fired — 2.7k lines in 10 new files + ~150 edited lines.
- Acceptance: rows 5, 10, 11, 11b, 23, 28, 28c, 37 re-derived as ref ⇒ mach ⇒ lit (CmpLitB.lean), each
  `refLit_<row> : forbiddenRef <row>` with `refLit_<row>_agrees : refLit_<row> = Lit.ref_<row> := rfl`.
  The S3a rows (CmpLitT.lean) still build unchanged (their `by decide` now decides `progS3bB`).
- Build: `lake build Weak.Prom.CmpLitB` green (closure = all Cmp files). `tools/ci/lint.sh`: only the expected
  drift findings (Weak/Prom is outside the roots by design; 10 new Cmp files added to that list).

## Statement (CmpMain.lean)
```
theorem rvwmo_complete (T : Test) (hT : progS3bB T = true) (hrun : T.runAll chs = some trs)
    (hc : condsOk ν trs = true) (hX : rvwmoRef (conc T trs ν g)) (hss : singleSize (conc T trs ν g))
    (_ : platformOrd (conc T trs ν g)) :
    ∃ run : PF.PFRun LP Unit,
      PF.validRun litStep (testImg T) () (progs T) (memOf (conc T trs ν g)) run ∧ promisesFirst run.evs ∧
      run.cfg.pcAgs.length = T.harts.length ∧ allDone run.cfg ∧
      (∀ h, machRow (run.trace h) = refRow (conc T trs ν g) h) ∧
      (∀ h r, regOf run.cfg h r = finalReg trs ν h r) ∧
      (∀ a n, finalMem (testImg T) (memOf (conc T trs ν g)) a n = refFinalMem (conc T trs ν g) a n)
```
Scope `progS3bB` (CmpDefs.lean `instrS3b`): S3a's subset plus Zalasr `l*.aq[rl]` / `s*.[aq]rl`, `lr`, `sc`
(success and failure: the reference's fork), AMOs (all ops), every aq/rl combination, sizes `szOk`. `memOf X`'s
message class is now `skCls` (AMO/SC `.excl`, release store `.rel`; INERT, checked by the machine's fulfil arms).

## Proof structure
- Invariant = S3a's `SimInv` (two STRICT conjuncts added, below) ∧ `ExtraInv` (CmpInvB.lean):
  `wVRel` below a past release-RCsc op (rule 7, past form); `wRes` = the most recent LR with no LR/SC instruction
  after it (pairing, rvwmo.adoc:114–116), with base, per-byte read timestamps, view ≤ the LR's (rule 8, M5).
  `wRmw` needs none (litmus emits the fused `LRmw`; `LInstr` clears the slot).
- S3a steps transport `ExtraInv` (`StepOk` now carries `keepRR`: wVRel, wRes unchanged; `stepOkB_of`).
- New steps: `sim_loadG` → `sim_loadAq`, `sim_lr` (rules 5, 6, 7; CmpSimLA/LB); `mem_storeG` + `stPreA_lt`
  → `sim_storeRl`, `sim_scOk`, `sim_scFail` (CmpSimW/WB/SC); `sim_amo` (CmpSimA).
- SC success: `scAx` pairs it with an LR; `pair_resv` makes that LR the machine reservation; `exclOk` from the
  atomicity axiom (and from `resvOk` for a byte the LR read from the image); rule 8 for the reservation view;
  forward view = own timestamp (rule 3, `fvOk_rmw`). AMO: read strictly below `ts`; `exclOk` because a write
  between the answer and the AMO would be a later load-value candidate.
- `stepI_new` (CmpSymB.lean): what each instruction appends (no LR/SC events from S3a instructions; store sizes;
  uniform sizes for NA-6 by `decide`). `refFromLitReg` (CmpLitB): ref ⇒ mach ⇒ lit for final-register outcomes
  (row 37).

## Edits to existing files (all marked `S3b`; minimal; no other workspace imports Cmp files)
- CmpDefs: `msgOf` class `skCls` (machine `rmw`/`sc` need `.excl`, a release `store` `.rel`); new `instrS3b`,
  `progS3bB`, `progS3bB_of_S3a`; header.
- CmpCtx: `HCtx.scope : progS3bB` (was `progS3aB`), `imgF_lt`.
- CmpInv: `SimInv.vrNew` and `fwdOk` gain a strict conjunct for a future load that is also a store (an AMO's
  read point must be strictly below its own write timestamp — machine `memStep.rmw`'s window); `keepRR` + lemmas;
  `StepOk` carries `keepRR`; `inv_nomem`'s `hvrn` type.
- CmpSimL (`.1` ×2), CmpSimF (strict part, `keepRR` ×2), CmpSimN (`keepRR` ×4), CmpSimLd (`keepRR`), CmpSimS
  (class, strict parts, `keepRR`): one-line fixes.
- CmpSim: imports the S3b steps; `instr_scope` → S3b; `sim` dispatches every S3b instruction with `ExtraInv`;
  `simInv_init` strict part; `sim_hart` passes `extra_init`.
- CmpMain: `progS3bB` in `rvwmo_complete`, `rvwmo_complete_exec`, `finalMem_eq`; `symRun_stSzB`. CmpRun: doc.
- CmpLit: `instrSz` covers the S3b accesses; `symRun_memSz` via `newEvOk_memSz`; `progS3bB` in
  `singleSize_of_uniform`, `refFromLit`, `forbid_of_lit`, `bridge_reg`, `obsReg`, `obsReg4/8`.

## Open items
- NA-6 still a premise: an LR/SC or AMO overlapping another access with a different footprint (e.g. `lr.d` +
  `sc.w` at one base) is mixed-size (S3c, [OWN.P5]).
- The Sail split AMO (`LAmoLd`/`LAmoSt`, `wRmw`) is not this theorem's front end (litmus `litStep` emits the fused
  `LRmw`); bridging is S1M-proof's `amoSplitFused` (M10(4)).
- The hypothetical RCpc `loadAqPc`/`storeRlPc` stay out (not RISC-V; no machine label). CMO not used (reads go
  through `loadOk`'s non-invalidate disjunct only), so the coordinator's `invalRead` fix does not touch S3b.
- `sim_amo` uses `set_option maxHeartbeats 1000000` (elaboration budget only).
- No other in-scope FORBIDDEN row has a `lit_` theorem (lbAcq, lbRel, armWeak, wsub, coh, seqT, rng, disjLists,
  lbfd have only `ref_` verdicts; mixSca is mixed-size; mpPtr is over `litStepF`).
