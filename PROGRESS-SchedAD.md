# SchedAD progress — track (a)'s concurrent adequacy over E-c's A/D machine variant

Owner ruling [OWN.P14] (track (a)); brief ~/dev/weak-orch/promising/SchedAD_prompt.txt; G4-review3.md §5 A-2,
§6 item 2; plan rev 7 §3 "Schedule lemma" (rev 5: non-A/D timestamp schedule), "`stage`, defined once", "Claim
(frontier)", "Test" (row 50 D-OOTA).  Workspace /home/bsdinis/dev/xv6iris-pcsl4.  NEW files only.

## Status (top): PASS — GREEN (2026-11-05).  No kill condition fired.
- Build: `lake build Weak.Prom.OwnAAdMP` green (271 jobs; closure = all five new files).  `#print axioms` of
  `adequacyAV`, `wpA_wpAV`, `own_mpAD`, `own_mpAD_run`, `row50_neg`: propext, Classical.choice, Quot.sound.
- Lint: only the expected drift findings for the five new files (Weak.lean not edited, per protocol).
- Lines: 1,754 NEW (OwnAAdLang 171, OwnAAdSched 342, OwnAAdWp 330, OwnAAdAdeq 542, OwnAAdMP 369).  0 edited.
- Named inputs: 0.  One GENERIC side condition of `adequacyAV`: `adEmit pstep` (an A/D label writes
  `update_PTE_Bits` of the bytes it read — M20 (6); AdMachine.lean leaves the A/D data to the program half as
  "emission").  Not program-specific; vacuous for a program half that emits no A/D label (`adEmit_liftV`).

## How `stage` / `fOk` treat A/D (plan §3 rev 5, verbatim definitions)
- `stageGeV M σ s`: every NON-A/D timestamp `t ≤ s` (`¬ Ad.adAt M t`) is fulfilled.  `fOkV` = `stageGeV` at
  `WF(h) = max vcap vwNew`.  A/D timestamps are never segment targets (`schedV` steps the author of the least
  unfulfilled NON-A/D timestamp).
- `cstepV.lab` (v2 labels incl. the variant's fetch arm): guarded by `fOkV` after the step, as `cstep`.
  `cstepV.ad`: NOT guarded; `ws` and the (v2-label) trace unchanged, promise consumed.  So kill condition 2
  ("own A/D fulfil above `stage` blocked by the frontier guard") cannot fire: the A/D arm has no guard, and the
  schedule takes A/D steps whenever they are the scheduled hart's next step.
- Kill condition 1 (`WF ≥ s ⊢ stage ≥ s` failing for a view-free A/D step): PROVED not to fail.  `schedV`
  re-proves the claim for every v2 step (`solo_floorV`: a later v2 fulfil's pre-view contains `WF`; A/D and fetch
  steps do not raise `WF`, `floorsV_mono`); an A/D step keeps every hart's claim (`fOkV_keep`).
- The shared state records only v2-label fulfils (`prjT` drops A/D entries), so `fulAt` sees only what `stage`
  counts.  A/D one-shots are SHOT at adequacy start (`pendsV_alloc`): "A/D writes carry no obligation"; the client
  gets `pend g t` for non-A/D `t` only; doom elimination at the end uses those shots.
- `stage ≥ V ⊢ validUpTo V` (`valid_frontV`, `valid_finV`): non-A/D `t` by its recorded `protoOk`; A/D `t` by
  `PO_adV` + `adExactV` from `Valid(t−1)`, fulfilled or not.  `PO_adV` is a PREMISE of `adequacyAV` (A0's PO-ad, a
  proof obligation); `adExactV` is PROVED from the run (`adExactV_of_run`, uses `adEmit`).

## What carries over
- `wpA_wpAV`: every v2 hart wp `wpA` of an A/D-free program (`liftV pstep`) entails the variant's `wpAV`
  (Löb over the two languages; `memStepV (.v l) ↔ memStep l` and `fOkV ↔ fOk` once `M` has no A/D message,
  `noAdL_of_run`).  `premiseV_of`: v2 `wpPremise` ⇒ variant `wpPremiseV`.
- `own_mpAD`: G4 (2)'s verdict (flag = 1 ⇒ x = 42) over EVERY valid run of the variant, via `adequacyAV` and the
  UNCHANGED `mp_premise`.  `own_mpAD_run`: the same via `validRunV_toV2` (an A/D-free variant run IS a v2 run)
  and `own_mp` — a cross-check.
- `row50_neg`: `¬ PO_adV proto₅₀ img₅₀ M₅₀` ("D clear", M[1] = WCad `P|D` = adUpd(memAt 0 p)) — carries over with
  the variant's A/D test; `row50_v2_vacuous` shows v2's `PO_ad` (isAd ≡ False) holds of the same data.

## Not done / caveats
- `adequacyAV` is for `D = Unit` (E-c's `validRunV_solo` is Unit-only); the language/wp are D-general.
- Not re-exported: A0 (iii′) fulfil-nodup and (v) `traceWf` (machine lemmas, not track-(a) content).
- No client uses the A/D arm of `wpAV_lift` (no PTE program; translation off); `own_mpAD` has no A/D message.
- The variant's fetch arm (`ownDoneV`) is E-c's reading (review 3 §7.4: STRONGER-side); reused as is.

## Files (Weak/Prom/, namespace `Weak.Prom.OAd`)
1. `OwnAAdLang.lean` — `isAdV`, `adExactV`, `PO_adV`, `protoOk_ad`, `stageGeV`, `fOkV`, `HWV`, `CExprV`, `cstepV`,
   view facts (`floorsV_mono`, `memStepV_v_some`, `memStepV_ad_at`).
2. `OwnAAdSched.lean` — `prjT`, `solo_floorV`, `solo_adAt`, `cfgOfV`, `msrV`, `cfg_stepV`, `sched_mainV`, `schedV`.
3. `OwnAAdWp.lean` — `valid_frontV`, `cFactsV_step`, `cFacts_keep`, `fOkV_keep`, `stAV`, `wpAV`, `wpAV_lift`.
4. `OwnAAdAdeq.lean` — `soloQV_fulfil`, `validRunV_fulfil`, `adEmit`, `adExactV_of_run`, `valid_finV`,
   `pendsV_alloc`, `wpPremiseV`, `adeq_coreV`, `adequacyAV`.
5. `OwnAAdMP.lean` — `liftV`, `noAdL_of_run`, `memStepV_toV2`, `validRunV_toV2`, `wpA_wpAV`, `premiseV_of`,
   `own_mpAD`, `own_mpAD_run`, `row50_neg`, `row50_v2_vacuous`.
