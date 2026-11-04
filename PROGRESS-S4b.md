# S4b progress — ownership track (b) "lock-scoped pull promises" (plan rev 7 §4, §8 S4b)

## Status (top): GREEN increment 6 (2026-11-03, part 2) — G4 (1a) PROVED with THE (b1) PULL; (2) re-proved on the
## real front end (part 1's caveats removed); (2′) PROVED; (5) restated.  NOT attempted: (1b), (1c), (3), (4).
## No kill criterion fired (≈7.8k new lines total ≪ 38k; no program-specific normal-form fact; 0 named inputs).
- Build: `lake build Weak.Prom.OwnLock Weak.Prom.OwnMP2 Weak.Prom.OwnMPL` green (new files only; NO existing file
  edited).  `#print axioms` of `Own.Lk.g4_lock`, `g4_lock_regs`, `Own.MP2.g4_mp2`, `Own.MPL.g4_mpOwnL`,
  `g4_mpOwnL_regs`, `g4_noDoubleClaimL`, `Own.lit_fetchBounded`, `Own.lit_invalFree`: propext, Classical.choice,
  Quot.sound.  No sorry / axiom / native_decide / opaque / implemented_by.
- R-b5: statements that DROP the `invalFree` premise after the coordinator's machine fix (load post-view absorbs the
  cited invalidate): `Nfr.nfR`, `Own.ownAdequacy`, `MPL.loadOk_byte` and its users (`mp_h1`, `h1_x`, `mp2_h1`,
  `Lk.hA`, `Lk.hC`, `Lk.hB`).  For litmus programs the premise is discharged (`lit_invalFree`), so no G4 verdict
  changes.

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

### Increment 4 — caveats removed for G4 (2): real front end (2026-11-03, part 2): DONE, green
- `Weak/Prom/OwnKit.lean` (~390 lines): track (b)'s LITMUS KIT over `wpO`: world `litOW img M` (`litStep`, value =
  final register file `litDoneR`), `wpT` (any trace), `hstepO_cases` (the two NF_R step kinds), `hstepO_quiet`
  (quiet labels are never write steps, never release-class: no language-state change), `hstepO_store/rmw/load`,
  the FULFIL FACT `fulO` (non-release-class: own promise in the prefix; release-class: `M[n]` appended in place),
  `rmwOk`; rules `wpT_drain`, `wpT_quietI`, `wpT_ld`, `wpT_sd`, `wpT_amo`, `wpT_fence`, `wpT_alui`, `wpT_br`,
  `wpT_end` (loads against `M.take σ.n`, writes against `M.take σ'.n`).
- `Weak/Prom/OwnLitSide.lean` (~170 lines): for EVERY valid run of ANY litmus test, `lit_fetchBounded` (PO-fetch:
  `litStep` emits no `LIFetch`) and `lit_invalFree` (no CMO message: `litStep` emits no `LCmo`).
- `Weak/Prom/OwnMPLDefs.lean` (~420 lines) + `Weak/Prom/OwnMPL.lean` (~560 lines): test `mpT` = track (a)'s
  `mpOwnT` text (`sd x5,(x6); fence rw,w; sd x7,(x8)` ‖ `ld x5,(x6); fence r,rw; ld x7,(x8)`, x5 = 42, image 0);
  part 1's protocol lifted to 8-byte footprints (`wrX`, `wrF`, `xVal`); per-byte read reasoning (`loadOk_byte`,
  `x_byte`, `mpOk_markX`).  **`g4_mpOwnL`**: every valid run, H1 finished with registers g ⇒ g[5] = 1 → g[7] = 42;
  **`g4_mpOwnL_regs`**: the same on the final configuration (`cfg.pcAgs[1]`).  **`g4_noDoubleClaimL`**: (5) for this
  state interpretation.  The release-class facts are machine facts (`relClass_store0`: first write; `relClass_fW`:
  plain store after `fence rw,w`), never program-text facts.  0 named inputs.
- Part 1's label-level files (OwnMPDefs/OwnMP) are kept (superseded for G4 by OwnMPL).

### Increment 5 — G4 (2′) (2026-11-03, part 2): DONE, green
- `Weak/Prom/OwnMP2Defs.lean` (~305 lines) + `Weak/Prom/OwnMP2.lean` (~515 lines).  Test `mp2T`: H0 as in `mpT` ‖
  H1 `ld x5,(x6); fence r,rw; sd x9,(x8)` (x9 = 2).  **`g4_mp2`**: every valid run, H1 finished with x5 = 1 ⇒
  `lastX2`: some T holds x = 2 (all 8 bytes) and no later message of the final memory writes x — H1's `sd 2` is the
  coherence-last write to x.  0 named inputs.
- **FINDING (R-b2, (b2-pull))**: with plan §3's release-class definition, H1's `sd` after `fence r,rw` is ALWAYS
  release-class (pre-view ≥ `vwNew ≥ vrOld`, and `vwOld = 0`: no earlier store) — `relClass_fRW` — so on track (b)
  it is appended IN PLACE, and the receiver's early data promise that (b2-pull) exists for is never FULFILLED for
  the plan's (2′) text: such promises are dead (appended before the claim) or backed (after) and never fulfilled.
  (2′) therefore does not test (b2-pull).  A text that does: the receiver stores first to an unrelated location
  (`sd z; ld flag; fence r,rw; sd x`): then `vwOld ≥ t_z` is not covered by `fence r,rw` (pw = false), the `sd x`
  can be non-release-class, hence promised early.  Not built (see "Next").
- Protocol additions over MPL: `sp` (x spoiled by a non-holder write: then x5 ≠ 1 or `bad`), `own1` (H1 wrote x as
  the holder: record (H1, 2) for good); ghost `γb` carries (bad, own1, sp).

### Increment 6 — G4 (1a) with THE (b1) PULL (2026-11-03, part 2): DONE, green
- Test `lkT` (OwnLockDefs.lean): both harts `amoswap.w.aq x5,x6,(x10); bne x5,x0,END; ld x7,(x11); addi x7,x7,1;
  sd x7,(x11); amoswap.w.rl x0,x0,(x10)` (lock word 4 bytes, counter 8 bytes, image 0; forward branches only, so a
  failed acquire gives up — finite runs, S3d separate).  **`g4_lock`** / **`g4_lock_regs`**: in every valid run, if
  both harts finished with x5 = 0 (both acquired), their final x7 differ (mutual exclusion of the counter CSs).
- (b1) DESIGN (as built): pure state `LkS` (OwnLockDefs.lean) — live cell `lc` (latest in-place release, or the
  image), lock state `free | pulled h u | owned h u`, the counter's record (holder, tenure start, latest message,
  value), dead sets `Dl`/`Dc`, `bad`, `spoil`, per-hart phase / recorded read / mark, counter `cnt`.
  * THE PULL (`lk_agent`, OwnLockAgent.lean): the agent appending an acquire-shaped message `u` of hart i on a FREE
    lock moves R (the counter's points-to half) into `pulled(i, u)` — R stays in the state interpretation on i's
    behalf and i becomes the counter's holder (tenure `u`), so i's counter promises are BACKED (b2-own "owned or
    pulled").  On a pulled/owned lock: an attempt (b1-none).  Other lock writes: dead (releases are in place).
    Counter writes: backed iff by the holder (b2-own) else dead (b2-none).  The split is TOTAL over any final memory.
  * THE AMO LEAF (`lk_acq`, OwnLockSteps.lean): an acquire whose byte-0 answer is 0 from a live message, with no
    other-hart write to the lock byte in (t0, ts) (atomicity), CONSUMES the pull (invariant `LockOk.taker`: such an
    AMO finds `pulled(h, u)`, u ≤ ts); an in-place (release-class) acquire on a free lock pulls itself; a nonzero
    answer gives up; a 0 from a dead message makes a ROGUE and SPOILS the protocol (a permanent dead lock message
    witnesses invalidity).
  * THE DEPOSIT: `amoswap.w.rl` is always release-class (`relClass_rl`), so in place: R goes to the new live cell
    (`lk_rel`).  The holder's read (`lk_ldc`) and store (`lk_sdc`) as in MPL, with holders changing.
  * Iris layer (OwnLock.lean): R = ghost half `hv γc (xr cr)`; `Rbox` (R's place: the state interpretation while
    free/pulled); per-hart phase ghost; one generic hart proof `hA … hG` instantiated for both harts.
- Files: OwnLockDefs (275), OwnLockAgent (315), OwnLockSteps (330), OwnLockSteps2 (436), OwnLock (935).

## Findings for the plan (part 2)
- **(2′) does not exercise (b2-pull)**: under plan §3's release-class definition, `ld flag; fence r,rw; sd x` by a
  receiver with no earlier store is release-class (`relClass_fRW`), hence in place; an early data promise of the
  receiver is never fulfilled.  A test that does exercise (b2-pull): give the receiver an earlier unrelated store.
- **(1b) needs (b1-def) / deferred deposits**: the release `fence rw,w; amoswap.w x0,x0,(a0)` is NOT always
  release-class on v2 — `relClass` compares with `vrOld` of the state AFTER the AMO's own read (`wrState`), and that
  read may return another hart's later attempt above `vwNew`.  So the release can be promised early, its deposit
  cannot be in place, and the agent rule "non-acquire lock writes are dead" fails for it.
- **(1c) needs a front-end extension**: xv6's `sext.w` (addiw) and `jal mycpu` are not in the litmus ISA; the release
  `sd zero,16(s1); fence rw,w; sw zero,0(s1)` IS release-class (`relClass_fW`) and would be deposited in place, but its
  lock message is `.plain` (not `.excl`), and the CS also writes the cpu field — a protocol variant.  Not built.

## G4 criteria (track b) — as of increment 6
- (i) (1a) ✓ `g4_lock`; (2) ✓ `g4_mpOwnL`; (2′) ✓ `g4_mp2`; (5) ✓ lemma form (`g4_noDoubleClaimL`); (1b), (1c),
  (3), (4) ✗ not attempted (findings above for (1b), (1c)).  0 named inputs throughout.
- (ii) `isLock γ lk s R` shape: NOT reproduced — the lock protocol is per test (R hard-wired as the counter's half;
  no saved-proposition slot, no lock-name parameter).
- (iii) ctxByte-shaped points-to: partial — per-location 8-byte record (holder, tenure, latest message, value) as a
  ghost half; no fractions `dq`, no context ξ, no per-address family.
- (iv) lines: part 1 3,093 + part 2 4,671 = 7,764.  S5 projection: FAILS under the default (E1′ rejected): PO-fetch
  unprovable for xv6, NF_R also needs `invalFree` (R-b5) and `D = Unit` (PO-dev); in addition xv6 needs (4)
  deferred deposits (`initlock`) and a per-lock generic library; cost counted as unbounded research (plan G4 (iv)).

## G4 criteria (track b) — as of increment 3 (superseded)
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

## Next (if continued, after part 2)
1. (1b): (b1-def) deferred deposits for a non-release-class release AMO; (1c): litmus front-end extension
   (addiw/`sext.w`, `jal`) in a new file + the plain-store release protocol variant; (3): ⟦·⟧-guarded racy read;
   (4): lock birth by plain stores with γ allocated at runtime (saved-prop slot).
2. Generic per-lock library (isLock shape) over the `LkS` mechanism.

## Next (as of part 1)
1. Generic ownership library over a ghost map (per-address records, release cells keyed by timestamp).
2. (b1) pull at AMO promise + AMO leaf → (1a) amoswap.aq/amoswap.rl spinlock with counter client.
3. (b2-pull) → (2'); then (1b), (1c) on the instruction front end (needs a `wpO` litmus kit).
