# MachFix progress — machine v2 fixes (R-b5 invalidate absorption; Sail `.error` havoc)

Stage tag: `MachFix` (markers `MachFix-R-b5`, `MachFix-havoc`).  Brief: ~/dev/weak-orch/promising/MachFix_prompt.txt.

## Status (top): BOTH FIXES DONE, GREEN (2026-11-04)
- `lake build` of every Weak/Prom module (140, incl. 6 new files) green.  No sorry / axiom / native_decide /
  opaque / implemented_by.  `Weak/Prom/MachFixCheck.lean` prints axioms of 28 key results: all
  `[propext, Classical.choice, Quot.sound]`.
- Regression runs (VM, 80 shards): label-level `MachOracle` cap 8 (with reference): 7869 tests, 0 differences vs
  `litmus/machine-cap8-D3.txt` (outcome sets, reference/herd comparisons, verdicts, node counts); cap 99 noref:
  7888 lines, 0 differences vs `litmus/s0rest/res-MachOracle.txt`.  Probes: G5x (`ProbeXRun`, the CMO / misaligned /
  amocas / no-device probes through Sail): all 17 lines identical to `litmus/s0exit/g5x-res.txt` (incl. CMO-INV,
  CMO-CLEANINV, CMO-FLUSHINV, CMO-PPO); G5 (`ProbeRun G5`, notoday): 9 identical to `s0rest/res-G5.txt`.  Extra:
  `MachSailOracle` cap 99 noref: 7888 lines identical to `s0rest/res-MachSailOracle.txt`; no test reaches a Sail
  `.error` node (0 HAVOC).  Expected differences: none outside the CMO-invalidate probes; observed: none at all (the
  probes' invalidate-citing load is each hart's last memory access, so the absorbed view orders nothing later).
- The havoc path of the explorer is exercised by a scratch `#eval` (not kept): one hart's path ends at
  `.stop "sail-error"` with its promises done + another hart finishes ⇒ valid candidate with `herr`; with an own
  promise outstanding ⇒ not havoc; a `trap` stop ⇒ not havoc; `msgLists` counts an error path as complete.

## FIX 1 (R-b5): the load's post-view absorbs the cited invalidate — FAITHFUL
Machine.lean: `invalReadAt` (the clause at a fixed `ti`; `invalRead = ∃ ti, invalReadAt …` unchanged), `bytesAny`,
`invalCite log ws vpre vi base tvs` (each byte normal or citing some `ti ≤ vi`; `vi = 0` or cited by a byte, so `vi`
= max of the cited `ti` for some choice), `readViewV`, `loadRunV` (= `loadRun` with the read point raised to `vi`).
Arms `load`/`rmw`/`amoLd`/`lr` take `∀ vi, invalCite … vi …` APPENDED (positional patterns unchanged) and post
`loadRunV … vi …`; `rmw` keeps COH/EXT on the `vi = 0` post-read state plus `vi < ts` (equivalent: `loadRunV_vRaise`
raises every view by at most `vi`, and the AMO writes the bytes it reads).  D-v2-5 closed; a cited byte's floor
stays `max(fl, ti)` (M9-style exemption, as before).
- New: `MachInval.lean` (zero/`vi0`/le/restrict lemmas, `vRaise`, `memStep.load0/lr0/amoLd0/rmw0`),
  `LitNoCmo.lean` (`noInval_of_noCmoLab`, `lit_noInval[PF|T]`, `progs_q`; `nfL`…`solo_q` MOVED verbatim from
  OwnLitSide.lean).  Explorer: `viCands`/`viOpts`, `succ` enumerates `vi` (only `0` without a CMO message); MachSound
  `memStepF` = the `vi = 0` step (certificates), new `memStepL` (+ sound); MachComplete `memStepL_complete` replaces
  `memStepF_complete`; MachSail `succAmoLd` mirror.
- Logic: CoreRules keeps `wpH_load`/`wpH_load_fwd`/`wpH_lr` under an auto-param `hnoinv` (no invalidate message
  in `M`) and adds the general `wpH_loadV`/`wpH_load_fwdV`/`wpH_lrV`; CoreKit/OwnKit/OwnAKit/OwnAFront kit load,
  AMO, LR rules: auto-param; per-test hart lemmas: auto-param; top theorems discharge it (`lit_noInvalT`,
  `litF_noInvalT`, `x_noInvalT`, `memOf_noInval` for Cmp).  Statements of the litmus / G4 / own_* theorems unchanged.
- invalFree: DROPPED from `Nfr.nfR`, `runSeg`, `runAll`, `schedule`, `memStep_restrict` (new premise `hvr`,
  derived from the self bound), `Own.ownAdequacy` (4 G4 call sites).  FINDING — not droppable as stated:
  `MPL.loadOk_byte`, `mp_h1`, `h1_x`, `mp2_h1`, `Lk.hA/hB/hC`: their conclusion ("no write to the byte in
  `(t, vpre]`") is false for a byte read through the invalidate clause, which the fix keeps; the premise is now only
  the litmus fact "no CMO message" (`lit_noInval`), not an NF_R escape.  The AMO hart steps `Lk.hD/hE/hF` now also
  take it (auto-param): the AMO post-state depends on `vi`.

## FIX 2 (havoc, [OWN.P8]/[OWN.P9] "Global")
- `MachHavoc.lean` (generic): `errCfg perr cfg`; `havocRun` = valid run whose final configuration has a hart at an
  error node; `havocs`; `allowedH O` = (∃ valid run with `O cfg`) ∨ `havocs` — after a havoc run every observation
  is allowed (`allowedH_of_havocs`); `forbiddenH_iff`: forbidden ⟺ no valid run satisfies `O` ∧ `¬ havocs`;
  `errCfg_persist`/`havocRun_of_prefix` (errors persist when `errStable`); `noErr_noHavoc`.
- `EmitHavoc.lean`: `sailErr h := ∃ e k, h.m = .impure (.error e) k`; `sailErr_stable : errStable pstepV2 sailErr`
  (PROVED: the `.error` arm is `False`, the parked FENCE.TSO step keeps `m`); `allowedSail`.  Emit.lean: comment
  only (the arm stays `False`, now documented as HAVOC); TableCv2 row `C-E.hnodeStep.m1.impure(error)` re-marked.
- `CoreHavoc.lean`: `pdoneE perr pdone` (an error node is DONE with the impossible value `none`), `ΦE` (`False` at
  `none`): the hart wp at an error node can only be proved via `⟦V⟧ False` — no rule, unreachability must be shown;
  `adequacyH` = A0 + `¬ errCfg perr run.cfg`; `noHavoc_of_adequacyH` = the havoc half of a forbidden verdict.
  A0 (`PF.adequacy`) itself is unchanged and speaks of valid runs only; its forbidden claims stand under havoc only
  with `¬ havocs` (all litmus front ends: `noErr_noHavoc`).
- Explorer/oracles: MachSail/MachSailX `MR.herr` (a path ends at `sail-error` with own promises done), an error path
  is a complete path for candidate memories, `SStat.havoc` (all harts end validly, some by havoc); MachSailOracle tag
  `HAVOC`, Sail verdict `HAVOC` (never forbidden); ProbeRun/ProbeXRun print `HAVOC` / `s=HAVOC`.
- OWNER QUESTION (HAVOC-PROM, recorded, not decided): the erroring hart is stuck, so a run where a hart reaches an
  error while ITS OWN promise is outstanding is not valid and is not havoc (the brief's "valid run reaching a Sail
  error").  Under [OWN.P8]'s "after `.error` the machine may do anything" it could still fulfil that promise; counting
  such runs would be WEAKER (the sound side) but needs A0 over runs with outstanding promises.

## Files touched (existing, minimal marked edits)
Machine, MachWf, MachFactor, MachExplore, MachSound, MachComplete, MachNota, MachNI, MachSail, MachSailX,
MachSailOracle, ProbeRun, ProbeXRun, TableCv2, Emit, NfrStep, NfrRun, OwnWp, OwnLang, OwnLitSide, OwnKit, OwnMPDefs,
OwnMP, OwnMPL, OwnMP2, OwnLock, OwnALang, OwnAKit, OwnAFront, OwnAMP, OwnAMP2, OwnALock, OwnALockCS, OwnALockFree,
OwnALock1b, CoreFwd, CoreRules, CoreKit, CoreKitV, CoreLit, CoreLit5, CoreLit6, CoreLitA, CoreLitAd, CoreLitCo,
CoreLitDR, CoreLitF, CoreLitH, CoreLitM, CoreLitMP, CoreLitP, CoreLitPI, CmpDefs, CmpSimA, CmpSimLB, CmpSimLd.
New: MachInval, LitNoCmo, MachHavoc, EmitHavoc, CoreHavoc, MachFixCheck.

## Log
- baseline build green (5 min from scratch); FIX 1 green; FIX 2 green; runs above; temporary `litmus-appx/` (herd
  log copy for the VM sync) and runner scripts removed from the workspace; the corpus was copied on the VM from
  pcsl5's `.lake/litmus/repo` into this tree's `.lake` (VM only, not synced back).
