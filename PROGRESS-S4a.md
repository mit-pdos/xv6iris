# S4a progress — ownership track (a), promises-first, frontier-gated resources (plan rev 7 §3, §4 G4, §8 S4a)

## Status (top): GREEN increment 3 (2026-11-03); no kill criterion fired
- K4: no program-specific normal-form fact (the schedule lemma is program-agnostic); 2,862 new lines (bound 19k).
- Build: `lake build Weak.Prom.OwnAMP Weak.Prom.OwnANeg` green (closure = all OwnA* files).
  `#print axioms`: `adequacyA`, `own_mp` — propext, Classical.choice, Quot.sound.  No sorry/axiom/native_decide.
- Workspace edits: NEW files only (`Weak/Prom/OwnA*.lean`); no existing file touched.
- G4 on track (a): (2) PROVED `Weak.Prom.OA.own_mp` (x's points-to moves H0 → flag slot → H1; 0 named inputs;
  finite runs, S3d separate [OWN.P4]); (5) PROVED `slot_two_readers` (+ `frontA_dup`).  NOT YET: (1a)/(1b)/(1c),
  (2′), (3), (4).
- Criteria: (ii) isLock shape — not attempted yet; (iii) ctxByte-shaped points-to — not yet (current `xPts` is a
  word-level "latest write + bag of later x-messages' `pend`"); (iv) 2.9k lines so far.

## Next (in order)
1. Kit: `wpKA_amo`, `wpKA_br`, `wpKA_alu(i)` (port of CoreKit's, with frontier/`shot`).
2. Points-to with a write FLOOR (hart-local view fact `fl ≤ vwNew ∨ ∃ j, fl ≤ coh(x+j)`) so a hart can WRITE after
   a doomed read (needed by the CS `ld c; addi; sd c` of (1)); machine lemma `coh ≤ vrOld ⊔ vwOld`.
3. Lock body over slots (one slot per lk message; uniqueness of the AMO reading a source from `exclOk`) → (1a),
   (1b), (1c) (needs `sext.w` = `addiw` in the litmus front end, or the Sail front end), then (2′), (3), (4)
   (saved-prop slot content for runtime γ).

## Files (Weak/Prom/)
1. `OwnALang.lean` — the concurrent language: shared state `CSt` (every hart's exact `(ws, P, τ)`), the write
   frontier `wfr = stFloor = max vcap vwNew` (plan §3 WF(h)), `fulAt`, `stageGe` (plan "stage ≥ s"; v2 has no A/D
   class, so every timestamp counts), THE FRONTIER CLAIM `fOk` (`WF(h) ≥ s ⊢ stage ≥ s`), `cstep` (one hart's
   machine-v2 step against `M`, GUARDED by the claim after the step), view facts `floor_le_fulPv` (a fulfil's
   pre-view contains the frontier), `floor_lt_ts`, `post_floor_le` (frontier after a fulfil at t is ≤ t).
2. `OwnASched.lean` — THE SCHEDULE LEMMA `sched` / `sched_main` (plan §3): given every hart's solo run against M
   and the partition, an execution of the guarded language reaches every hart's final state with its trace.
   Schedule = step the author of the least unfulfilled timestamp (the plan's segments), then anything.
3. `OwnAWp.lean` — ghost names `AGN`; `hartA`; per-message one-shots `pend g t` / `shot g t` (pre-allocated for
   t ∈ 1..|M|); the doom box `doomInv` (`dpend`/`dshot`) with `doom`; state interpretation `stA` (hart halves,
   claim of every hart, `□ ∀ fulfilled t, shot t`, facts `cFacts` or doom); `wpA`; THE LIFTING LEMMA `wpA_lift`
   (one ▷ + £1 per step; hands the client the pre-state facts and THE FRONTIER RULE `frontA` = shots up to WF and
   `Valid(WF)`; requires `shot g t` at a fulfil of t).
4. `OwnAAdeq.lean` — allocation (`harts_alloc`, `pends_alloc`: big sep over the M-indexed family, R-a5),
   `adeq_core`, THE CONCURRENT ADEQUACY `adequacyA` (exports (i) termination, (ii) Ψ at every prefix, (iii)
   partition, (iv) Valid, (v) traceWf), proved via the schedule lemma + `wp_strong_adequacy_gen`; doom is
   eliminated at the end (every t fulfilled ⇒ shot ⇒ the box holds no `pend s`).

5. `OwnAKit.lean` — the litmus kit over `wpA` (`lhA`, `wpKA`; one-label rules q1/load1/store1/drain; instruction
   rules `wpKA_ld`, `wpKA_sw`, `wpKA_fence`, `wpKA_end`): every label step's continuation runs under `|={⊤}=>` with
   `£ 1` and the frontier of its pre-state; a fulfil hands back `shot`; any obligation may be doom.
7. `OwnAMPDefs.lean` / `OwnAMP.lean` — G4 (2): test `mpOwnT`, message classes (x-messages → x's bag, flag
   messages → deposit slots, the rest → dead), setup `mp_setup`, hart proofs `mp_h0` (deposit at the release-class
   flag store), `mp_h1`/`mp_h1_tail` (claim after `fence r,rw` via the frontier rule; owned read or doom), bundle
   `ownGF`, `mp_premise`, THE VERDICT `own_mp`.
8. `OwnANeg.lean` — G4 (5): `frontA_dup`, `slot_two_readers`, `slot_two_readers_tok`.
6. `OwnALib.lean` — dead messages (`deadInv`, `dead_doom`, `dead_shot`), DEPOSIT SLOTS (`slotInv`, `slot_alloc`,
   `slot_deposit`, `slot_claim`: claim token = iris-lean `token`), THE OWNED READ `load_owned` (pure: a load whose
   floor covers the latest owned write `lw` returns `lw`'s bytes or reads a message above `lw` touching the
   location), `loadOk_weak`.

## Design decisions (for the coordinator / G4 comparison)
- "stage" is NOT a run-parameterised ghost value: the frontier claim is a GUARD on the language step, proved by
  the schedule lemma for every valid run; the Iris model stays ordinary (R-a2 avoided).
- R-a1 (owner's relaxed read may return a future message of the next owner) is handled by the DOOM BOX: a hart that
  holds `pend s` of an unfulfilled message `s` may surrender it; `s` can never be fulfilled, the run is not valid,
  and the persistent `dshot` discharges all later obligations; adequacy rules doom out.  Points-to (next increment)
  will carry the `pend` tokens of the later messages to its location.
- Deposit slots: the lifting lemma requires `shot g t` at t's fulfil, so `inv N (pend t ∨ shot t ∗ R)` forces the
  author to deposit R exactly at its fulfil (plan §3 deposit); saved-prop slots (plan rev-4 design) layer on top.

## Next
- OwnALib: points-to `x ↦ v` (latest write + the `pend` tokens of later x-messages), read/write rules, deposit
  slots (saved props), then G4 (2) MP with ownership transfer.
