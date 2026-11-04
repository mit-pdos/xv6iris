# S4a progress — ownership track (a), promises-first, frontier-gated resources (plan rev 7 §3, §4 G4, §8 S4a)

## Status (top): GREEN increment 8 (2026-11-04, part 3: G4 (1c) and (3) proved); no kill criterion fired
- K4: no program-specific normal-form fact; 9,307 lines in Weak/Prom/OwnA*.lean (bound 19k; 2× = 38k).
- Build: `lake build Weak.Prom.OwnAHold` green (closure includes OwnALock1c and every part-1/2 file).
  `#print axioms own_lock1c`, `own_lock1c_excl`, `own_hold`: propext, Classical.choice, Quot.sound.
  No sorry/axiom/native_decide/opaque/implemented_by.
- Workspace edits: NEW files only in part 3 (OwnALock1c*.lean in namespace `OA.C`, OwnAHold.lean in `OA.H`);
  no part-1/2 file and no shared file touched; does not depend on `invalRead` beyond the existing
  `loadOk_weak`/`cld_cases`/`cmo_dead` uses (pcsl6's R-b5 rebase: OwnALock1cLib/CS, as (1a)/(1b)).
- G4 on track (a), 0 named inputs each, finite runs (prefix lemma S3d separate, [OWN.P4]):
  - (1c) PROVED `own_lock1c` (+ `own_lock1c_excl`): xv6's exact text `li a4,1; again: mv a5,a4 (c.mv = add);
    amoswap.w.aq a5,a5,(s1); sext.w a5,a5 (addiw); bnez a5,again; sd a0,16(s1); <ld;addi;sd counter>;
    sd zero,16(s1); fence rw,w; sw zero,0(s1)`; same `qLk` statement as (1a).  The PLAIN `sw` is release-class
    through `fence rw,w` (its pre-view `stPreA ⊒ vwNew ⊒ vrOld ⊔ vwOld`): the deposit happens at a plain store's
    fulfil.  The cpu field `Lk+16` is a second bag in the lock resource `Rs s = cPts(lw ≤ s) ∗ pPts s`.
  - (3) PROVED `own_hold`: hart 0 runs xv6's acquire/release ops (lock word + cpu field), hart 1 runs xv6's
    `holding()` (racy `lw` → `beqz`; racy `ld 16(s1)` → `sub; seqz; beqz`) and acquire's panic test; hart 1
    never panics.  FINDING: needs neither the frontier rule nor ownership on track (a): content classification
    (all of M known) + `dead_doom` decide the racy value unguarded at the read (bytes of 0 or 0x3000, never
    0x3100).  The frontier is needed only for resources and for protocol facts content does not determine.
    The release-side variant (`holding()` = 1 for the holder) is NOT proved (needs a lock-word/cpu-field
    points-to with latest write for the holder; ≈ 0.6k).
  - (1a), (1b), (2), (2′), (5) PROVED (part 2).  NOT DONE: (4) pipealloc / runtime γ / saved-prop slots.
- Criteria: (i) 7 of 8 targets ((4) missing); (ii) PARTIAL (blocked on (4)); (iii) EXPRESSIBLE; (iv) below.

### Criteria, re-measured 2026-11-04 (part 3)
- (ii) unchanged: `lkCtx g M tk` is a persistent invariant-only handle (as `isLock`'s `inv lockN …`), and (1c)
  shows its body works for xv6's text (plain release, cpu field).  Still FIXED `R` (the M-indexed `Rs`) and a
  constant `Lk`: `isLock γ lk s R` with runtime `γ`, generic `R : CtxId → IProp` needs (4).  SavedProp API is in
  the pinned iris-lean (`saved_prop_alloc/update_halves/persist/agree`, Iris/Instances/Lib/SavedProp.lean) but
  `SavedPropG` is not in `ownGF` yet.
- (iii) unchanged (EXPRESSIBLE): `ctxByte ξ a dq v` ↦ `∃ lw, ⌜M[lw] has v at a⌝ ∗ [∗ later a-msgs] pend ∗
  ⌜lw ≤ view⌝`; `dq` needs fractional bags (pend is exclusive).
- (iv) Lines: OwnA*.lean 9,307 (part 1 2,862; part 2 3,770; part 3 2,675: (1c) 1,944 of which ≈ 500 duplicated
  class-dependent lock lemmas, (3) 727).  S5-delta projection, revised: lock body over runtime saved-prop slots +
  address-keyed classes 2–3k; ctxByte-shaped per-byte pend bags + readAU/writeAU leaves 4–6k; xv6 acquire/release
  leaves 1–1.5k ((1c) exists at litmus level); boot-time M-indexed setup (every byte's bag to its boot owner)
  2–4k; REPLACING FREE MODE (below) 2–4k; (4)'s deferred deposits 1.5–3k; proof-text edits 3–5k; total
  ≈ 16–26k, not counting S3c/S3d.

### Dead-messages risk of free mode for xv6 with arbitrary user code (assessed 2026-11-04)
- Where the litmus proofs use free mode: a read of a message no text can fulfil (`deadInv`, `dead_doom`): junk
  lock values (AMO read a non-0/1 word; `lk_acq`, `lk_src`), own junk lock messages in `lk_chain`, non-counter
  bytes in the critical-section read (`lk_cs*`), cmo/invalidate sources (`cmo_dead`), and (3)'s bad cpu values.
- For xv6 almost nothing is dead: (a) user code is arbitrary, so every plain message to a user-writable page
  with any data is fulfillable; (b) kernel text writes data-dependent values everywhere (`memmove`, `copyin`),
  and `kfree`'s `memset(pa, 1, PGSIZE)` WRITES JUNK INTO FUTURE LOCK WORDS (pipealloc's page), so junk lock values
  are text-written, not dead; (c) a content classification of "what kernel text can write" would be a
  program-specific input (kill criterion).  So S5 cannot use free mode; free mode stays a litmus device.
- What S5 needs instead, concretely: AN OWNER FOR EVERY BYTE'S PEND TOKENS.  At adequacy start, the pend of
  every message to byte `a` goes to `a`'s boot-time points-to (kernel image/boot heap ownership); the points-to
  of `a` carries the pends of all later messages to `a` (as `cPts`), and moves with ownership (kalloc/kfree free
  list, locks, process memory).  Then: (i) an owner's relaxed read of a later message dooms with the pend it
  holds (R-a1, as now); (ii) a NON-owner racy read (holding(), unlocked flag reads, xv6 audit row 1) cannot doom
  — the pend is someone else's — so it must use the core's ⟦t⟧-guarded pure protocol facts (π.okMsg +
  ValidInduction, S2) instead of content classification: (3)'s proof does not transfer, its statement does
  (protocol: "the cpu field holds 0 or the holder's cpu"); (iii) junk in lock words is excluded by (4)'s
  deferred-deposit/publication argument (birth `sw zero` coherence-after the junk, acquirer's source after the
  birth), not by deadness; (iv) shared read-only bytes need fractional bags (no later messages ⇒ empty bag, so
  only mutable shared bytes are an issue).  Risk: (ii) means every racy read site needs a Proto entry
  (pure, program-level but per-location, not program-specific normal form), and (iii) is exactly the untested
  R-a4.

### Part 3 files (Weak/Prom/, namespaces `OA.C`, `OA.H`)
23. `OwnAHold.lean` (727) — (3): texts `p3o`/`p3h`, test `t3`, content classes (`shp`, `isF`, `isDd`), pure
   `pc_byte`/`pc_read` (the racy read's value), `setup3`, `h0_run`, `h1_run`/`h1_doomed`/`h1_end`, `premise3`,
   THE VERDICT `own_hold`.
18. `OwnALock1cDefs.lean` (365) — text `p1c`/test `t1c`, classes (`lmP`: `excl` or `plain`; `pmP` cpu field;
   `isDd` = none of lock/counter/cpu), `pBag`/`pPts`, `Rs` (two bags), slots, `lkCtx`, `obag`, `*_notDd`.
19. `OwnALock1cLib.lean` (292) — `lk_src`, `lk_chain`, `lk_claim`, `lk_acq` (copies; proofs verbatim).
20. `OwnALock1cFree.lean` (250) — kit rule `wpKA_alu` (reg-reg ALU, for `c.mv`), helpers, `lk_free1c`.
21. `OwnALock1cCS.lean` (524) — `lk_cpu1`, `lk_cs1c`, `lk_cs2_1c`, `lk_cpu0`, `lk_fence1c`, `lk_rel1c`.
22. `OwnALock1c.lean` (513) — `lk_loop1c`, `lk_hart1c`, `lk_setup`, `lk_premise1c`, THE VERDICTS.
Design note: the duplication (Lib ≈ 290 lines + Defs ≈ 200) is the price of not editing part-2 files; S5 would
parameterise the lock lemmas by the class predicates instead (≈ −500 lines).

### Criteria (ii)–(iv), measured 2026-11-03
- (ii) `isLock γ lk s R` (MachCSL/Lock.lean:3325, persistent `inv lockN (lockBodyM …)` + floors).  Track (a)'s handle
  `lkCtx g M tk` IS persistent and the lock body is invariants only (image slot `iSlot`, one `rSlot r` per release
  message, `deadInv`s) — no floors.  But (a) the slots are allocated at adequacy start for the M-indexed family, so
  `R` is FIXED there (`Rs` = the counter's points-to); a generic `R` (and `R : CtxId → IProp`) needs the plan's
  saved-proposition slots σ_t (G4 (4), not built); (b) `lk` is a constant of the classification (`Lk`); a runtime
  lock needs the classes keyed by the lock address of the `initlock` that created it.  So the STATEMENT shape
  `isLock γ lk s R` is reproducible only after (4): γ ↦ (tk, slot names), lk ↦ the classification key.
- (iii) ctxByte-shaped points-to (`ctxByte ξ a dq v`: `a ↦ₕ (e :: H)` + `keyAt ξ e.t`).  Track (a)'s points-to is
  `cPts lw` = "latest write `lw` (pure, M-indexed) ∗ the `pend` of every later message to the location"; per byte it
  is `∃ lw, ⌜M[lw] holds v at a⌝ ∗ [∗ later a-messages] pend`, and `keyAt ξ e.t` becomes a HART-LOCAL view fact
  `lw ≤ vrNew/ldPre` (in this kit a pure fact about the hart state carried by the proof, not a resource).
  Expressible; `dq` fractions are not (the bag of `pend`s is exclusive; read sharing needs fractional bags).
- (iv) Lines: OwnA*.lean 6,632 (part 1 2,862; part 2 3,770: free mode in part-1 files ~120, loop front end + kit
  390, lock library shared by (1a)/(1b) 1,450 (Defs 382, Lib 292, Free 181, CS 446, Acq 149), (1a) 490, (1b) 825,
  (2′) 495).  S5-delta projection for track (a), rough: lock body over
  runtime-allocated saved-prop slots + address-keyed classes 2–3k; ctxByte-shaped per-byte bags and readAU/writeAU
  leaves over the kit 4–6k; (1c)/xv6 acquire-release leaf lemmas 1.5k; the M-indexed setup for a kernel (every
  address's messages to an owner's bag) 2–4k; proof-text edits (10 files unfolding `↦ₕ`, 21 calling
  readAU/writeAU, 7 touching `lkFloor`) 3–5k; total ≈ 13–20k lines, not counting S3d/S3c.
  RISK for S5: free mode needs DEAD messages (no text can fulfil them); with arbitrary user code almost no shape is
  dead, so lock-word reads of unexpected messages must instead be refuted by the OWNER of that address's bag — every
  byte of memory needs an owner of its messages' `pend`s (the classification): the big S5 item.

### Design findings of part 2 (for G4)
- R-a1 "doomed continuations": after a doom the hart must still fulfil its later writes (the lifting lemma needs
  `shot t`), but the doomed branch may lack the resources holding their `pend`.  FIX (general, OwnAWp): a second
  mode of the doom box — FREE MODE `dfree`, entered only with a DEAD witness (`g.dd d`: a message no hart's text can
  fulfil; the client picks `dd`, adequacy takes it as a parameter `Dd`); a fulfil hands back
  `fulT g t = shot g t ∨ (dfree g ∗ ⌜¬ g.dd t⌝)`.  Sound: at the end of a valid run the dead witness is fulfilled,
  but its fulfil could not use free mode (`¬ dd`) and its `pend` is in the box.  Ordinary doom (R-a1 reads of the
  next owner's future message) keeps the reader's resources: its own later store lies above `coh ≥ the read
  message` (THE WRITE FLOOR, `loadBytes_coh`), so the surrendered `pend` is never needed again.
- The lock (OwnALockDefs): no "stage"/"who reads s" ghost needed: the claim token of release `s`'s slot is the token
  of `nxtL M s` (the first later write to the lock word, a pure function of M); an AMO at `ts` that read `s0` proves
  `nxtL M s0 ts` per step from `exclOk` (other harts), its coherence floor (own writes at or below it) and its
  own-message bag (own writes above it are unfulfilled, but the frontier `≥ ts` shows them fulfilled: absurd).
- Release-class is used as plan §3 defines it: the `.rl` AMO's pre-view contains `vwOld ≥ ts_c`.

## Next (in order)
1. (4) pipealloc shape: `SavedPropG` (and a GName-valued ghost for runtime γ) in a new bundle; per-t saved-prop
   slots σ_t + `rOf_t` deferred-deposit slots pre-allocated (R-a5); lock L2 born by `sw zero` over `kfree` junk
   (`memset 1`), published through lock L1; the deposit at L1's release names L2's runtime handle.  Estimate
   3–5k lines (two lock instances; reuse OwnALock1c* parameterised by the lock address).
2. (3′) release-side `holding()` = 1 for the holder (≈ 0.6k).
3. Parameterise the class-dependent lock lemmas (OwnALockLib/Acq vs OwnALock1cLib) by the class predicates
   (≈ −500 lines).

## Files (Weak/Prom/)
16. `OwnALock1b.lean` — (1b): text `p1b`, free walker `lk_free1b`, `lk_cs1b`/`lk_cs2_1b`, `lk_rel1b` (fence) +
   `lk_rel1b_amo`, `lk_loop1b` (claim at `fence r,rw`), THE VERDICT `own_lock1b`.
17. `OwnAMP2.lean` — (2′): test `mpW`, classes (`isW`: H1's own message), `mw_setup`, `mw_h0`, `mw_h1`,
   `mw_h1_tail`, THE VERDICT `own_mp2`.
9. `OwnAFront.lean` — the LOOP FRONT END (new program half `xStep Xs` over `LP`: backward branches, `addiw`;
   `litW_x`, `litAg_x`/`litAg_xn`) and kit rules `wpKA_alui`, `wpKA_rmw1`, `wpKA_amo`, `wpKA_brx`, `wpKA_addiw`.
   Recorded decision: NOT an edit of RefProg/MachLitmus (`Instr` is matched exhaustively in 14 shared files);
   `addiw` is an `XI` constructor whose `LP.prog` placeholder is `.nop`.
10. `OwnALockDefs.lean` — (1a) text/test, message classes (`isA`, `isR`, `isC`, `isJ`, `isDd`), the chain `nxtL`,
   `qLk` (the mutual-exclusion invariant), bags, `cPts`, `Rs`, `iSlot`, `rSlot`, `lkCtx`, `obag`.
11. `OwnALockLib.lean` — `cld_cases` (owned counter read, R-a1 cases), `lk_src`, `lk_chain`, `lk_claim`.
12. `OwnALockFree.lean` — `ddL` (dead predicate), `lk_free` (free mode walks the text, Löb).
13. `OwnALockCS.lean` — `lk_cs` (ld: clean / R-a1 doom / free), `lk_cs2` (addi; sd moves the points-to),
   `lk_rel` (release AMO deposits `Rs r`).
14. `OwnALockAcq.lean` — `lk_acq` (the acquire step: value 1, or 0 with the claimed `Rs s0`, or free).
15. `OwnALock.lean` — `lk_loop` (Löb over the spin loop), `lk_hart`, `lk_setup`, `lk_premise`, THE VERDICTS
   `own_lock1a`, `own_lock1a_excl`.
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
