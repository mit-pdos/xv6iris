# S4b progress — ownership track (b) "lock-scoped pull promises" (plan rev 7 §4, §8 S4b)

## Status (top): GREEN STOP POINT 2026-11-03 — NF_R proved; track-(b) concurrent logic + adequacy proved; G4 (2)
## and (5) proved; G4 (1a)/(1b)/(1c)/(2')/(3)/(4) NOT attempted.  No kill criterion fired (3.1k lines ≪ 38k; no
## program-specific normal-form fact; no named input).
- Build: `lake build Weak.Prom.OwnMP Weak.Prom.NfrRun` green (all new files; no existing file edited).
- `#print axioms` of `Nfr.nfR`, `Own.ownAdequacy`, `Own.MP.g4_mpOwn`, `Own.MP.g4_noDoubleClaim`:
  propext, Classical.choice, Quot.sound.

## Plan of work (order fixed by the brief)
1. NF_R lemma for machine v2 (program-agnostic), premises (P1) trivial, (P2) fetch-bounded, (P3)/(P4) vacuous on v2.
2. Track (b) logic pieces.
3. G4 targets in the order (2), (5), (1a)/(1b)/(1c), (2'), (3), (4).

## Log

### Increment 1 — NF_R lemma: DONE, green (2026-11-03)
- Files: `Weak/Prom/NfrStep.lean` (533 lines), `Weak/Prom/NfrRun.lean` (840 lines). Build:
  `lake build Weak.Prom.NfrRun` green; `#print axioms Weak.Prom.Nfr.nfR`: propext, Classical.choice, Quot.sound.
- **Statement** (`Weak.Prom.Nfr.nfR`): for machine v2 with `D = Unit` (no device fabric; plan §4 "The device fabric
  is excluded until PO-dev"), every `validRun pstep img () ps evs cfg` with
  (P2) `fetchBounded pstep img ps cfg.pcLog evs` and `invalFree cfg.pcLog` has an `evs'` with
  `nfRun pstep img () ps evs' cfg` (SAME final configuration) and `traceOf h evs' = traceOf h evs` for all h.
  `nfRun` = `nfSteps` from `pmInit` + no promises: every release-class write step is immediately preceded by the
  promise of its own message and fulfils the top of the log (`nfSteps.rel`); no other state step is release-class.
- `relClass ws l` = plan §3's definition (write pre-view ≥ vrOld ⊔ vwOld of the state immediately before the write;
  for the fused AMO that state includes the read half) for all five write arms (store, rmw, amoSt, sc, cmo).
- Premises: (P1) trivial on v2 (no `lat`); (P3), (P4) vacuous (v2 has no walk / A/D arm, [OWN.P3]); (P2) =
  `fetchBounded` (at every release-class write at r of hart h, every earlier fetch source of h is < r).
  PO-fetch per program: `fetchBounded_ofImg` (every fetched byte has timestamp 0, PA-0) — the G4 programs.
- **New escape found (R-b5): the invalidate clause.** `invalRead` (Machine.lean) lets a load cite an invalidate-class
  CMO `ti` ABOVE every view of the hart (`ti` is existentially chosen; D-v2-5: the post-view does not absorb it).
  So a load before a release can depend on a message above the release, which an NF_R prefix lacks — the same shape
  as the fetch escape.  NF_R takes `invalFree M` (no inval/flush CMO in M) as a premise; G4 programs have no CMO.
  Machine-side fix to consider (not made; S1M owns Machine.lean): bound `ti` by the read point (the text's "i
  precedes r" in gmo), or absorb `ti` into the post-view (D-v2-5 currently WEAKER on purpose).
- Proof shape: restriction lemma `memStep_restrict` (converse of MachFactor's `memStep_extend`); self bound
  `memStep_self` (`bnd ws = vrOld ⊔ vwOld ⊔ wIfr` bounds every view, read and fulfil); schedule invariant `Inv`
  over per-hart remaining solo runs; induction on |M| − |log|, least first release each round.
- Spin loops: NF_R is over FINITE valid runs (as `validRun`); infinite runs need the prefix lemma (S3d), separate.

### Increment 2 — track (b) concurrent language, wp and adequacy: DONE, green (2026-11-03)
- Files: `Weak/Prom/OwnLang.lean` (349 lines), `Weak/Prom/OwnWp.lean` (~210 lines).  `lake build Weak.Prom.OwnWp`
  green; `#print axioms Weak.Prom.Own.ownAdequacy`: propext, Classical.choice, Quot.sound.
- Language (plan §4 "Pull rule"): thread pool = N harts + ONE PROMISE-AGENT thread over a prophecy world `OW`
  (program half, value map, image, final memory M); state `OSt` = log length n (log = `M.take n`), promise sets,
  recorded values.  Hart step = one NF_R step (`hstepO.plain`: non-release step against the prefix; `hstepO.rel`:
  release-class write appending its own message `M[n]` and fulfilling it IN PLACE, atomically); agent step =
  append `M[n]` as a promise of its author; `fin` = a hart with a value and no outstanding promise stops.
- `nf_sim` + `fin_steps`: every NF_R run (NfrRun.lean) is an execution of the language.
- `wpO X e Φ` (one ▷ + £1 per step, MaybeStuck) under a CLIENT state interpretation `X : OSt → iProp` (the place
  for points-to, release deposits, pulls); `wpO_hart_lift` (the `wpHart_lift` shape, plan §7);
  `wpO_agent`: "the promise agent's wp is the invariant" — if every agent step preserves X the agent is safe.
- `ownAdequacy`: X with `X σ0`, the agent obligation, every hart's wp and a final extraction
  (`n = |M|`, all promise sets empty ⊢ ⌜φ done⌝) give φ of the final value map of EVERY valid, fetch-bounded,
  invalFree run (D = Unit), through `nfR`.  No named assumption.

### Increment 3 — G4 targets (2) and (5) on track (b): DONE, green (2026-11-03)
- Files: `Weak/Prom/OwnMPDefs.lean` (543 lines: program, protocol `mpOk`, pure step lemmas),
  `Weak/Prom/OwnMP.lean` (~630 lines: ghost bundle `mpGF`, state interpretation `Xmp`, hart wps, agent obligation,
  final extraction, machine side conditions, theorems).
- **(2) `Own.MP.g4_mpOwn`**: every valid machine-v2 run of `H0 = st x 1; fence rw,w; st flag 1` ‖
  `H1 = ld flag; fence r,rw; ld x`: if H1 finished with answers g then g[0] = 1 → g[1] = 1.  x's points-to (a ghost
  half `hv γx (xr ⟨hold, tstart, tstar, v⟩)`) is held by H0, updated by its store, DEPOSITED into flag's release
  cell at the in-place release step (`hstepO.rel`), CLAIMED by H1 (designated claimant, owns the token `γc`) at its
  flag read, and then gives `ld x = 1`.  Data promises need write permission: the agent marks an x-message backed
  iff its author is the current holder (b2-own), else DEAD (b2-none); every flag message the agent appends is dead
  (releases are in place).  Dead messages are never fulfilled, so at the end of a valid run there are none
  (`mpOk_final`); reading one sets `bad`.  PO-fetch per program: `mp_fetch` (the program fetches nothing);
  `invalFree`: `mp_invalFree` (no CMO messages).  0 named inputs.
- **(5) `Own.MP.g4_noDoubleClaim`**: `Xmp σ ∗ hv γx a ∗ hv γx b ⊢ False` — at most one thread holds the deposited
  points-to, and claiming needs the unique token (`token_exclusive`).  Track (b) needs no pre-allocated invariant:
  no reader can read the release before its deposit (in place).  This is a lemma about the logic's resources, not
  a 3-hart run theorem.
- FIDELITY NOTES: label-level program half `tpStep` (one memory label per access; no LRegW/LInstr, no dependency
  sources), byte width 1 (plan says `sd`/`ld`), image all 0.  The instruction front end `litStep` and the S2 kit are
  not used (the kit is over S2's per-hart wp, not over `wpO`).

## G4 criteria (track b) — as of this stop point
- (i) (2) ✓, (5) ✓ (lemma form); (1a), (1b), (1c), (2'), (3), (4) ✗ not attempted.  (1a–c) need the (b1) PULL at the
  acquiring AMO's promise (the agent pulls R into `pulled(γ, ts)` when the lock's latest message below ts is an
  in-place release); (2') needs (b2-pull) (agent claims W(x) for the designated receiver for x-messages appended
  after the flag release); (4) needs deferred deposits; (3) needs ⟦·⟧-guarded racy reads.  The mechanism in
  `OwnMPDefs` (holder / backed / dead / leftover record + release cell) is the base for them but is written for
  ONE location and ONE release cell; it is not yet a generic library.
- (ii) `isLock γ lk s R` shape: NOT reproduced (no lock target done).
- (iii) ctxByte-shaped points-to: partially — a byte points-to with a view bound (`tstar`) and a holder; no
  fraction `dq`, no context ξ, single location.  A per-address family over a ghost map is the obvious extension.
- (iv) Lines: 3,093 new (NF_R 1,373; language+wp+adequacy 551; MP target 1,169).  S5 projection: per plan §4/G4
  (iv) track (b)'s xv6 projection FAILS under the default (E1′ rejected): PO-fetch is unprovable for xv6 (fetches of
  exec'd code have no upper bound), and NF_R additionally needs `invalFree` (R-b5, new) and `D = Unit` (PO-dev).
  Cost of a fetch-/inval-tolerant NF_R: unbounded research, as the plan says.

## Risks hit
- R-b5 (NEW): invalidate-clause escape (`invalRead`'s `ti` above every view); NF_R premise `invalFree`.
- R-b4: as planned — (P2) fetch-bounded is a premise; discharged per program only.
- R-b2 (open, the main unknown): totality of the agent's case split — only (b2-own)/(b2-none) and the release cell
  exist; (b1) and (b2-pull) are designed (plan §4) but not built.
- Fidelity of the targets: label-level programs, byte width (see above).
- Spin loops: all statements are over FINITE valid runs (NF_R and `ownAdequacy`); the spinlock targets also need
  the prefix lemma (S3d), separate.

## Next (if continued)
1. Generic ownership library over a ghost map (per-address records, release cells keyed by timestamp).
2. (b1) pull at AMO promise + AMO leaf → (1a) amoswap.aq/amoswap.rl spinlock with counter client.
3. (b2-pull) → (2'); then (1b), (1c) on the instruction front end (needs a `wpO` litmus kit).
