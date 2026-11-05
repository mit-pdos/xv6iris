# E-b4 progress — E-a4's LOCK LIFECYCLE test on TRACK (b) (lock-scoped pull promises)

Brief: ~/dev/weak-orch/promising/Eb4_prompt.txt (+ wave4_common.txt); owner ruling [OWN.P16] (context.md item 24):
"you should probably run the same experiment on track b".  New files only: Weak/Prom/OwnBE4*.lean, namespace
`Weak.Prom.OB.E4`.  No existing file edited, no root edit.

## Status (top): PASS — PROVED (2026-11-05)
- `Weak.Prom.OB.E4.own_be4 (M) (run) (hrun : PF.validRun (xStep xs7) img7 () (progs t7) M run) :
  ∀ h, q7 M (memEv (run.trace h))` — E-a4's `t7`, `q7` (= `qMx ∧ qGd`: per critical section mutual exclusion (1c),
  no field load reads junk or the image (4)) in BOTH lifetimes, for EVERY hart, finished or not.
- STATEMENT CHECK (Weak/Prom/OwnBE4Check.lean): `example : type_of% own_be4 = type_of% Weak.Prom.OA.E4.own_e4 := rfl`
  — green (no weakening, no extra hypothesis).  OwnBE4.lean itself does not import any OwnAE4 proof file.
- `#print axioms own_be4`: propext, Classical.choice, Quot.sound.  0 named inputs (`hnoinv` = the front end's
  machine fact `x_noInvalT hrun`).  No premise on the run (no fetch bound, no "harts finish"): via `nfRF`.
- Builds: `lake build Weak.Prom.OwnBE4Check` green (340 jobs).  `tools/ci/lint.sh`: only `drift`, one per new file
  (not reached from a root — no root edit, as E-a4; the coordinator wires them).  grep sorry/admit/axiom/
  native_decide/opaque/implemented_by over OwnBE4*: docstrings and `#print axioms` only.

## Lines (wc -l, same breakdown as E-a4)
- **B-0 (one-time trace adequacy; OwnBE4Lang/Adeq/Kit, every lemma tagged `[retype …]`): 772** (317 + 194 + 261).
- **Lifecycle: 3,968** (target 3,000 missed by 32%; hard stop 5,500 not reached; 3,000 checkpoint written at the
  time; 4,000 not reached):
  * mechanism 2,720 — protocol defs 281 (OwnBE4Defs), agent obligation 369 (OwnBE4Agent), step lemmas 1,855
    (Steps 261, Steps2 205, Steps3 372, Steps4 313, Steps5 357, Steps6 347), Iris layer 215 (OwnBE4Iris: state
    interpretation `XX`, `xstep`, agent/final glue, initial state `inv_init`, the new rule `wpX_alu`);
  * text-generic block library 393 (OwnBE4Gen: flag wait `waitB`, xv6's acquire spin loop `amoB`, cpu-field store
    `pcB`, machine-state step facts, `wpH_gen`) — reusable as S5 leaves;
  * per-text proof 705 (OwnBE4H1 323: an acquirer's round; OwnBE4H0 382: hart 0's round);
  * setup + verdict 150 (OwnBE4 140, OwnBE4Check 10).
- Comparison: E-a4 3,235 on top of E-a2 2,206 (≈ 5.4k for the same ground on (a)); (b): 772 + 3,968 = 4,740 on top
  of S4b (which had no generic lock, no runtime-born contended lock, no trace adequacy).  Nothing compressed to fit.

## Lifecycle design on track (b) (as built)
- State interpretation `XX M γ σ = ∃ S ls, ⌜Inv M σ S ls⌝ ∗ ½ ls 0 ∗ ½ ls 1 ∗ ½ ls 2`; each hart owns the other half
  of its STAGE RECORD `Loc` (round, stage, tenure start, publication timestamp, CS-load answers, hart 0's close floor
  and done flags).  Every hart step is one pure lemma about `Inv` lifted by `xstep`.
- The protocol `PS` is a pure state machine over the PREFIX: lifetime `lt`; lock `dead | free | pulled h u |
  owned h u`; field holder/tenure/latest live write; robust dead `Dr`; dead `Dc`; in-place flag records
  `pubT k`, `dnT i k`.
  * dead phase: hart 0 is the holder; its kfree junk, initlock and field stores (promised or in place) are BACKED;
  * PUBLICATION (hart 0's in-place `sb`, `inv_pub`) = the DEFERRED DEPOSIT (b1-def): `dead → free`; hart 0's
    unfulfilled lock-word promises become robust dead, its unfulfilled field promises dead;
  * THE PULL (agent, `agent_p`): an acquire-shaped message on a free lock → `pulled i (n+1)`, `i` holds the field;
  * the AMO leaf (`inv_amoS`): byte 0 read zero from a LIVE ZERO `t0` through a clean window ⇒ the taker invariant
    (`tk1` promised / `tk2` in place) makes the hart the owner; a robust-dead source spoils (below);
  * in-place release (`inv_rel`): `owned → free`; the holder's unfulfilled field promises dead;
  * CLOSING release (`inv_close`, hart 0 holding, both done flags): `owned 0 → dead`, `lt+1`, hart 0 KEEPS field and
    word (holder stays 0), its close floor `cf` := the release.
- Field: `later` (every field message above the latest live write is dead or the holder's own pending promise);
  `pairOk` at the CS store from "no dead message in the prefix" + reclassification of the holder's other pending
  promises (`inv_csst`); an own pending field promise read early is reclassified dead (`inv_csld`).
- Trace (B-0): `GoodT` — hart 0's trace has no field load; with no dead message in the prefix both acquirers'
  traces satisfy `q7`; the final state (`pr = ∅`) refutes every dead message (`inv_final`).
- SPOILED mode: `Inv = WF ∧ (Good ∨ ∃ robust dead pending)`; robust dead = a shape no text fulfils from a promise
  (`¬ okS`) or hart 0's lock-word promise appended outside its dead phase (below its next close floor `cf`, kept by
  hart 0's own coherence).  A rogue acquire (zero read from such a message) switches to it; `rob_ful` keeps it.
- Release class (B-5): plan §3's `relClass` suffices (every release, publication and done byte is a plain store
  after `fence rw,w`: `relClass_fW`); `relClassPre` not needed.

## The four questions
- **Windows needed?** No.  Nothing classifies the FINAL `M` by lifetime.  Lifetimes are delimited at runtime by the
  in-place publication and closing release in the prefix; the only timestamp-delimited ingredients are the taker
  invariant's premise `pubT lt < ts` (an acquire of this lifetime lies above its publication) and hart 0's close
  floor `cf` in the robust-dead predicate — both runtime state of the prefix (convergence entry (i)).
- **Death protocol needed?** An equivalent, without resources: the closing release requires both done flags, and
  the invariant `dnk` (a done byte of round `k` in the prefix ⇒ its author's round counter > `k`) plus the stage
  clauses give that no acquirer is in the lifetime; then `dead` keeps hart 0 as holder.  No participation tokens,
  no death mark, no parts returned (convergence entry (ii)).
- **Birth `sw zero` vs release `sw zero`?** Nobody tells them apart.  Both are LIVE ZEROS; the resource is never
  attached to a message: it is deposited into the lock STATE at the publication and taken through the pull + taker
  invariant from a clean window over ANY live zero.  Whether a hart-0 zero word is backed is decided by the agent at
  append by the PROTOCOL PHASE (dead ⇒ backed, published ⇒ robust dead), and the closing release is recognised at
  the author's in-place step by the protocol state (hart 0 holding, both done flags) — not by shape or reader.
- **Does the agent's split at `n` read `M` above `n`?** No.  `agentOk` uses only `M[n]` and the current state; no
  boot family indexed by timestamps of `M` (three ghost records allocated at start).

## What (b) made easier / harder than (a), and what it needed that (a) also needed
- Avoided: windows over the final `M`, shape-only birth slots, saved-proposition handles, release/death slots, the
  death mark, per-hart parts returned through done bytes, boot token families, the doom box.  Lifecycle transitions
  are state-machine steps; the taker invariant resets trivially at each publication.
- Also needed (equivalents of (a)'s): a never-fulfilled class with a timestamp floor (`Rob`/`cf` ≈ junk/"beyond the
  window"); "participants have left" before the death (`dnk` ≈ returned participation); own-pending-read handling
  (≈ (a)'s own-bag doom); the forward-bank invariant `fI` for flag-read floors.
- Harder: the agent split must be TOTAL over any `M` (shape classes `okS` + phase); a SPOILED mode with a robust
  witness (a rogue acquire must not break the invariant); every hart-step kind re-proves the whole invariant
  (23 clauses) — the mechanism (2.7k) is mostly that frame work, Owicki–Gries style.

## Convergence toward (a) (mandatory entries)
- (i) timestamp-delimited lifetime facts (`pubT lt < ts` in `tk1`, hart 0's close floor `cf` in `Rob`) — runtime
  prefix state, NOT a classification of `M`, NOT consulted above `n`.
- (ii) `dnk`: a done byte carries "its author left the round" — the role of (a)'s participation one-shots, as a pure
  invariant.
- (iii) robust dead messages never fulfilled ≈ (a)'s junk/doom (`lkJunk`), here certified by text shape and hart 0's
  own coherence.
- OW.M above `n`: not consulted.  Timestamp-indexed boot families: none.

## S5 / S5c consequences for (b)'s isLock
- isLock on (b) = a per-lock record in `X` (lifetime, lock state, holder/tenure/latest write, dead sets) plus a
  per-hart stage record; birth = the dead→free deposit at a publication; death = a closing release under a
  "participants left" invariant; reuse = the next dead phase at the same address.
- The agent split is total here because the address map is STATIC per test (lock word, field, cpu field, flags;
  everything else robust dead).  xv6 needs a DYNAMIC registry address → protocol (kalloc'd pages): not per-byte
  ownership, but a per-object protocol registry in `X` — the B-3 cost; the B-3 kill did not fire for `t7`.
- The death condition generalises to "every participant's stage is past this lifetime", learned through a channel
  (here done bytes; in xv6 refcounts under the lock).
- Per-step invariant re-proof is the dominant cost; S5 would want generic frame lemmas per protocol component.

## Track-neutral imports from (a) (machine/PMsg level; for audit)
- OwnAE4Gen.lean (`Weak.Prom.OA.E4`): `fI` (forward-bank invariant), `wsM` (views/coherence grow), `wsM_refl`,
  `wsM_trans`, `fI_ld`, `fI_st`, `wsM_ld`, `wsM_st`, `wsM_fence`, `fI_of`, `wsM_eq`, `le_fwd`, `postA_st` — facts
  about `PState` posts of machine v2 steps, no logic.
- OwnAPipeH1.lean (`OA.P`): `postA` (the post-state of `amoswap.w.aq; sext.w; bnez`), `postA_vr`.
- OwnALib.lean `OA.byteAt_off`, OwnAEBase.lean `OA.E.byteAt_none`: `PMsg.byteAt` arithmetic.

## Every `Weak.Prom.OA.*` identifier used (grep-able)
- Test: `p0 pA b0 bA t7 xs7 img7 img7_eq xOf_p0 xOf_pA atI`; verdict: `q7 q7_noLd q7_snoc q7_ld q7_pair pairOk
  latestC3 isC3 cmP3 gd noLd noLd_nil noLd_snoc isCLd isCSt clsB clsB_iff clsB_of cAt5 Lk Ct Pc L1 J own_e4`
  (`own_e4` only in OwnBE4Check's type comparison); front end (OwnAFront): `XI xOf xNext xStep xNext_q xNext_plain
  xNext_br xNext_addiw addiwV pc_lt_x x_noInvalT`; plus the track-neutral list above.  No IProp/GName/AGN/SV/
  Proto/HW decl, no window, slot, `zw`, `bth` or `l2_val`.
- Track (b) reused: NfrFetch `nfRF`; OwnLang `OW OSt hstepO agentStep authorAt upd`; OwnKit `fulO rmwOk hstepO_*`;
  OwnKitX `xOW XP xp_of xlit xp_end`; OwnLock1c `Lk1c.pend amo_x5 addiw_sext ofBytes4_lt`; OwnMPL `relClass_fW
  loadOk_byte relPrG`; OwnLock `loadRun_coh_j cohBelow_get`; OwnMP `au memByte_take take_get`; Core* kit lemmas.

## Files (Weak/Prom/)
- B-0: `OwnBE4Lang.lean`, `OwnBE4Adeq.lean` (`ownAdeqT`), `OwnBE4Kit.lean`.
- Lifecycle: `OwnBE4Defs.lean`, `OwnBE4Agent.lean`, `OwnBE4Steps.lean` … `OwnBE4Steps6.lean`, `OwnBE4Iris.lean`,
  `OwnBE4Gen.lean`, `OwnBE4H1.lean`, `OwnBE4H0.lean`, `OwnBE4.lean` (THE VERDICT `own_be4`), `OwnBE4Check.lean`.
