# E-c progress — G4 deciding experiment E-c: track (b)'s NF_R with an A/D arm

Owner ruling [OWN.P13] (context.md item 20, "Do B)"); brief ~/dev/weak-orch/promising/Ec_prompt.txt;
G4-review2.md §5.5, §6 B-1′, §7 "E-c".  Workspace /home/bsdinis/dev/xv6iris-pcsl4.

## Status (top): PASS — GREEN (2026-11-04).
- `Ad.nfRAd` (plan §3 class) and `Ad.nfRAd_pre` (S4b3 `relClassPre`): every valid run of the A/D variant
  (`D = Unit`) has an NF run with the same final configuration and per-hart traces — NO premise (no A/D-bound
  (P4), no fetch bound).  Fix (i).
- `Ad.ownAdequacyAd`: `ownAdequacyF`'s client-premise shape (X, agent obligation, hart wps, final extraction), the
  agent obligation now over `agentStepA`; NO premise on the run.
- `Ad.Witness.witness` / `witness_nf`: a concrete valid run (A/D at ts 2, then a release at ts 1, one hart) — the arm
  is exercised and its NF run keeps the trace.
- `#print axioms` (Weak/Prom/EcCheck.lean) of all five: propext, Classical.choice, Quot.sound.  0 named inputs.
- Lines: 1,922 NEW (AdMachine 155, NfrAd 1,218 — ≈700 of it NfrFetch's schedule re-typed to `VLabel`, ≈200 the
  solo factorisation for the variant; OwnAd 467 — ≈300 OwnLang/OwnWp re-typed; AdWitness 76; EcCheck 6).
  0 edited lines in existing files; Machine.lean untouched; no root edit.
- Builds: `lake build Weak.Prom.EcCheck` green (241 jobs; covers AdMachine, NfrAd, OwnAd, AdWitness).

## The arm (AdMachine.lean header has the quotes and marks)
- Fused label `VLabel.ad base tvs data`, fulfil `ts` of a `.ad`-class own promise: each read byte holds its value at
  `t`, `t < ts`, no write by ANY agent to the byte in `(t, ts)` (supervisor.adoc:1622–1624; M20 (2)) — FAITHFUL; no
  COH, no pre-view but the read sources; NO post effect (M20 (3) rev 5) — FAITHFUL for speculative A updates
  (supervisor.adoc:1625–1627, the program may emit it anywhere).  PA-5-ord (:1635–1640) and M20 (1)'s PA-1 view
  contribution of a non-speculative update not enforced — WEAKER (they only RAISE views).  D exactness (:1628–1630)
  off — WEAKER-or-FAITHFUL.  Fused read+write: FAITHFUL for behaviours (no view effect), as `LRmw`.  `adData` is
  emission (not checked).  The arm also requires `0 < ts` (redundant in valid runs: `promWf`).
- WCad: `PClass.ad := .cmo .clean 0` with non-empty data — an encoding, because `PClass` is closed and Machine.lean
  may not be edited; no v2 arm fulfils it (`memStep.cmo` needs `data = []`), `cmoAt` never sees it (length 0).
  REBASE NOTE: if the mainline adds a real `PClass.ad` constructor, this `def` must be dropped (name clash).
- Fetch: the own-store exemption excludes A/D writes (`ownDoneV`): an A/D write is not a po-earlier store
  (M20 Reference "a gmo store outside po").  Needed for `fetchViewV_cut`; FAITHFUL to the `fetchView` reading.

## Which fix, and what changed
- FIX (ii) IS IMPOSSIBLE (not merely harder): the witness run (one hart: `ad` at ts 2, then release store at ts 1;
  valid because the A/D write raises no view) has trace `[ad@2, rel@1]`; an NF run fulfils the release in place at
  log length 0→1, after the `ad` step, so that step runs at log length 0 < 2.  Deferring it reorders the hart's
  trace (and the program half `pstep` gives no commutation).  This is the plan's "commutation lemma ruled out".
- FIX (i), built: `nfStepsV.adF` — an A/D step whose timestamp is ABOVE the log is checked against the final `M`
  (the A/D analogue of E-b's `fet`), hart state and cut promise set unchanged; `nfStepsV.promF` — the agent appends
  an A/D message with NO promise owner.  Same events (`.prom i m`), so traces are unchanged.
- NfrFetch → NfrAd: ONE invariant clause changes — an own message above the prefix is still promised OR is an A/D
  message (`hartInvV`); `promOneV` picks `prom` vs `promF` from the author's solo state; `runSegV` gains the A/D
  case (restriction if `ts ≤ |log|`, else `adF`); `runSegV`'s 4th output is the weakened clause.  `bndF`, `fwdB`,
  `RCOk`, `memStep_selfF`, `memStep_restrict` are REUSED unchanged (the A/D arm moves no view).
- OwnLang/OwnWpF → OwnAd: `OSt` REUSED UNCHANGED.  New `hstepA.adF` (no state change), one new disjunct in
  `agentStepA` (append an `.ad` message, no owner).  `nf_simA` adds the two cases.
- NO pre-fulfilled bookkeeping anywhere: neither the NF configuration nor `OSt` records which A/D messages were
  fulfilled early; the scheduler's choice `prom`/`promF` is meta-level (from the solo runs).  The hart's `adF`
  step learns only pure facts about `M` (as `hstepO.fetch`); no resource about `M[t]`, `t > n`, is needed.

## The review's claim, checked (G4-review2.md §5.5)
"No read in the segment can depend on the deferred write (it would raise vrOld above r)": TRUE for every explicit
read (load, LR, AMO read: post-view ≥ source, `memStep_selfF`) and for every log window of the segment (`exclOk`,
`writesIn`, COH all below `bndF < r`).  Two reads are NOT so bounded and are replayed against `M` instead: fetches
(E-b) and the A/D update's OWN implicit read (its sources are bounded only by `ts`).  One more interaction found:
the fetch view's own-store exemption must not cover an A/D write fulfilled early (`ownDoneV`).

## Verdict on convergence (B-1′)
No convergence at the NF_R/adequacy level: the A/D arm costs one prophecy-fed hart arm + one owner-less agent
append, no future per-timestamp bookkeeping (B-1′'s kill condition does not fire).  What remains is client-side:
the agent obligation for an owner-less A/D append must preserve `X` when `M[n]` (an A/D write) enters the prefix
— an A/D-tolerant PTE points-to plus `adData` (a pure `M` fact; the A/D read is the prefix-latest by atomicity).
That is PO-ad's analogue and exists on track (a) too.  B-2 (fetch wp rule for exec'd text) is unchanged.
Not tested: walks (P3; no walk arm, translation off), the hart-side wp lifting lemma for the new arm, any client.
