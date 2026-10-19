VERDICT: NOT SATISFIED

# Review R44 of `notes/weak-allocproc-plan.md` (rev 54): revised row 6l design, increment 19, Q-6M-GFVAL

Reviewer: one-off design advisor + reviewer (advisory only: no builds, no proofs, no git/jj, no subagents). Read at the
working tree `../xv6iris-weak` on 2026-10-18 (after the merges rev 54 names): `Weak/SilCand.lean`, `SilWalk.lean`,
`SilOrd.lean`, `SilAgree.lean`, `SilKillT.lean`, `SilSite*.lean`, `CertZ18/23/24/34/35.lean`, `GraphFetchN2.lean`,
`LockFacts.lean`, `LockFacts3.lean`, `TsoShadow.lean`, `WeakMem.lean`, `WeakAxiomatic.lean`, `MachCSL/Lang.lean`,
`MachCSL/TsoMem.lean`, `CapF1.lean`, `MachOfPf.lean`; the three worker reports; R43; [OWN.106]–[OWN.108].

**Why NOT SATISFIED.** I would not sign off on launching rows 6l / 6m / 19 as briefed, because a check I ran while
designing the gate (PART 0) shows that the REALIZATION TARGET itself — a lockstep member on a TSO-store log
(`SilCand.stepS` appends every store at its step; MachCSL δ1 keeps `tv := top` at an acquire) — cannot replay a class
of RVWMO executions that xv6's nested locking produces. That makes `silentQ`/`rmwQ` (row 6m) unsatisfiable at those
executions, makes `noStuck` false for EVERY po-respecting gate (so F6l-1/F6l-2 are symptoms, not the disease), makes
increment 19's option (A) `candScaTS` FALSE and (C) unavailable, and means row 1's narrow δ1 (inc 15–16b, green) does
not by itself let the twin map onto MachCSL. The owner has not seen this shape ([OWN.100]/[OWN.103]/[OWN.105] were
ruled on the 2-hart cross-spin only). The design below is therefore in two parts: a core that is correct under either
resolution (land it), and an owner decision Q-6L-SB between a TSO member with SKIPS plus a multi-tick clock boundary
(K, recommended, ≈ 4–7k) and a store-buffer MachCSL (P, faithful, XL). Nothing below is a model-text change.

## PART 0 — FINDING F44-1: a lockstep member on a TSO-store log cannot replay "store buffered past an acquire"

### 0.1 Spec first (riscv.cat)

xv6's release is `fence rw,w; sw zero,0(s1)` (`LockFacts.lean:16-21`, `relPc`), its acquire `amoswap.w.aq`
(`LockFacts.lean:9`), no fence (`fenceCensus`: seven fences, none in `acquire`). riscv.cat orders a plain store `w`
before a po-later access only by: rules 1–3 (same address), rule 4 (a FENCE between them with pw and the matching
successor bit), rule 6 (`po;[RL]`), rule 7 (RCsc both), rule 13 (pipeline). `[AQ];po` (rule 5) orders the ACQUIRE's
successors after it, not its predecessors. So a release store `w′` may sit in gmo AFTER the hart's next
`amoswap.w.aq` on another lock and after every later load until the hart's next `fence` with pw (the next
`release`'s `fence rw,w` orders `w′` before THAT store; a later `fence r,rw`/`iorw` drains). This is the standard
"store buffer not drained by an acquire" of RVWMO, explicitly in scope ([OWN.2]: W→W reordering allowed).

**Litmus 1 (2 harts, nested locks; both spin once more than TSO allows).** Hart 1: `release(b)` [w′]; `acquire(e)`
[A1, succeeds]; `acquire(d)` → `holding+0x0` reads `d.locked` [r1] and/or `amoswap.aq d` [F1, fails]. Hart 2:
`release(d)` [w″]; `acquire(c)` [A2, succeeds]; `acquire(b)` → [r2]/[F2 fails]. rf: r1/F1 read hart 2's old
`A_d2` (value 1), r2/F2 read hart 1's old `A_b1`. Required gmo: `A1 < r1 < w″` (rule 5; load value: `w″` is co-after
r1's source, not po-earlier), `A2 < r2 < w′`; `w′ <po A1` and `w″ <po A2` are UNORDERED (no rule). Witness
`A1 A2 r1 r2 F1 F2 w′ w″` — cat-consistent (I checked rules 1–13, load value, atomicity `rmw ∩ (fre;coe) = ∅` with
F1's write co-adjacent to `A_d2`). On any TSO-store log (stores appended in program order, per hart) the member
needs `log(A1) < log(w″)`, `log(A2) < log(w′)` (a stale read/failed AMO can only read what is not yet appended) and
po gives `log(w′) < log(A1)`, `log(w″) < log(A2)`: a cycle. No walk order exists.

**Litmus 2 (3 harts; defeats any acquire FLOOR, not only `top`).** Hart 2: `release(z)` [w″′]; `acquire(d)` [A_d2].
Hart 1: `holding+0x0`/`amoswap` on `d` reads `A_d2`'s 1 [r1]; later `release(y)` [R_y] (its `fence rw,w` orders r1
before R_y). Hart 3: `acquire(y)` [A_y3, source R_y]; `acquire(z)` → reads `z.locked` = 1 stale [r3] (source: hart
2's old `A_z2`; `w″′` co-after). gmo: `A_d2 < r1 < R_y < A_y3 < r3 < w″′`, with `w″′ <po A_d2` unordered — consistent
(hart 2's release of `z` is still in its store buffer while it acquires `d`; hart 1 sees `d` held and releases `y`;
hart 3 takes `y` and still sees `z` held). TSO-store log: `log(w″′) < log(A_d2) < walk(r1) < log(R_y)` (po, rf,
po) and hart 3's stale read needs `log(R_y) ≤ floor_3 < log(w″′)` under ANY floor ≥ the acquire's source position:
a cycle. So weakening MachCSL's acquire floor from `top` to the source position (a "δ1′") does not help; the store
side must move.

Both shapes are reachable in xv6 (nested `acquire` is everywhere: `wait`/`exit` take `wait_lock` then `p->lock`,
`scheduler`/`sched`, `kfree` under `kmem.lock` after a `release`, `wakeup` loops over `p->lock`). The visible
difference is one extra failed spin iteration (or `holding`'s long arm) per hart — benign for xv6, fatal for a
LOCKSTEP member.

### 0.2 Where it bites in the tree (file:line)

- `SilCand.silentOk` (`Weak/SilCand.lean:86-94`): `SilCand.ownExcl σ.msLog i ≤ q` — the silent write's position is
  bounded below by the LOG position of the hart's own latest exclusive message (A1's write). Faithful under
  "log = gmo", but the log also forces `w′ <log A1w` (po append), which gmo does not; the conjunction is the cycle.
- MachCSL δ1 (`MachCSL/Lang.lean:553-556`): the stale exclusive read needs `σ.tv cpu ≤ tvn`; `MState.afterExcl :161`
  sets `tv := top` at an `aq` read and `MState.store :209` `top+1` after the pair. Plain loads (`:544-548`) need
  `tv ≤ tvn` too — so `holding+0x0`'s stale replay ([OWN.108]) is NOT MachCSL-realizable after an acquire either.
- `mstep`'s `MStepStore` (`Weak/WeakAxiomatic.lean:149-153`) and `MState.store` append at the step: `CertZ35.crossSpinNo`
  is the 2-hart instance of the general fact; the silent arm only removed the AMO's own append.
- `TsoShadow.scaOkT :519` / `shFloor :193`: the shadow floor after an acquire is the log top — increment 19 (A)'s
  `candScaTS` would be asked to hold where it is false (Litmus 1: r1 at hart 1 after A1).

### 0.3 Consequences for rows 1 / 6l / 6m / 19

1. **Row 6m's `silentQ`, `rmwQ` and the pinned-stale `ordQ`** (`Weak/SilSite.lean:313-331`) are per-step premises
   that are FALSE at Litmus 1/2 under every walk order: the twin step the datum must supply does not exist. They
   cannot be "discharged by 6l"; nor can they be NAMED soundly (a false named premise = a vacuous theorem, the
   [OWN.94] `walkPolicyCZ` situation again).
2. **R43's `noStuck` (and my gate) is FALSE** for any gate that respects po and appends stores at their step — F6l-1
   (pinned loads) and F6l-2 (pre-registration sources) are real but secondary; [OWN.108]'s "replay stale" is the
   right idea and is still blocked by MachCSL's floor.
3. **Increment 19**: (A) is FALSE (0.2); (C) "realized members project to registered M2 candidates" does not hold
   for a member that replays stale loads (their `scaOkT` fails), and under K below it becomes TRUE by construction
   (every member load is latest) — see "## Increment 19".
4. **Row 1 (δ1)**: inc 15–16b are sound and faithful as MachCSL rules (more behaviours, fewer than RVWMO), but they do
   not deliver "twin runs map onto MachCSL step for step" ([OWN.105]'s promise) beyond the 2-hart shape. Do NOT start
   inc 19 on this basis.
5. **What survives unchanged**: the kill consumers (`SilKillT.cycleKillCore :98-141` consumes `agreeW4` through
   `SilAgree.agreeW4OfRPS :46` — CertZ24's "modulo failed acquires" agreement is ALREADY the transport's interface),
   windowed `lockCoSP`, `CertZ23.ordCoSP`, the gate record idea, `SilSiteTab`/`SilSiteTaint` (static), the census,
   `CapFetchProv`, CertZ24–33 (the skip route, green, `Weak.lean:775-798`).

### 0.4 Resolutions (spec first; marks are w.r.t. riscv.cat; sizes unverified)

- **(K) TSO member with SKIPS + a multi-tick clock boundary (recommended).** Keep MachCSL's store side; the member
  reads LATEST everywhere (so the registered W4 `machRunOfPfRun` realizes it — no twin W4); where GF spins once more
  than a TSO member can (a failed `amoswap`, a `started` spin iteration) or takes `holding`'s long arm on a stale 1,
  the member SKIPS that private window (CertZ24–33's padded member + `relLag`, re-converging at the next successful
  `amoswap` / loop exit / `holding`'s return). The block that killed this route (CertZ34: `mtime`/`mip` drift,
  `PROGRESS-W10N2p.md:800-830`) falls to ONE MachCSL change: a hart may tick its clock any number of times at an
  instruction boundary (`riscvStep (tick : Bool)` `MachCSL/Lang.lean:310-312` ticks at most once; add a tick-only
  boundary step, or `tick : Nat`). Spec: `mtime` is a platform real-time counter, not an instruction counter — more
  faithful than one-tick-per-step; `minstret` already has "no lasting drift" (w3 :803); interrupts are OFF across every
  skipped window (`push_off` precedes `holding` and the spin; the boot spin runs with `sstatus.SIE = 0`), so the
  member catches up before the first interrupt-enabled boundary. FAITHFUL for the GF quantifier (every cat-consistent
  GF gets a member; the machine is a proof device). Size ≈ 0.5–1.2k MachCSL (tick arm + `swp_tick_clock_hs` reuse +
  Vtest + W4 `simStep` tick case) + 3–5.5k Weak. Retires: the silent twin as the realization (Sil* stays green, dead),
  row 1 inc 19, `silentQ`, [OWN.103] (R).
- **(P) RVWMO-TSO store buffer in MachCSL + lockstep.** Per-hart FIFO of pending plain stores landing at any later
  machine step, drained by a `fence` with pw∧sr, by a same-address access, by `.rl`/RCsc, NOT by an AMO; own loads
  forward from the FIFO; the twin candidate gets the same buffer; the walk gates LANDINGS ("land `w` only when every
  GF reader of `w`'s co-predecessor is realized" — progress by the fence before every release store). FAITHFUL (a
  strict subset of RVWMO's orders, every xv6 GF representable as far as I can see). Size: XL (every store WP rule,
  the interpretation's `hist`/`log`/`ownPub`, adequacy, W4; 8–15k MachCSL + 3–5k Weak). Keeps lockstep (no skips).
- **(N) a NAMED premise** "no release store is buffered past the hart's next acquire" — STRONGER than RVWMO (excludes
  Litmus 1/2), exactly what [OWN.100] rejected for (β). Cost 0. Listed for completeness only.
- **(B) `readAt` and the L2′ facts at the twin weak-WP tier** (w1's option (B)) — WEAKER header (a second program
  logic's proof of xv6 stays a premise); and it does not remove F44-1 (the twin itself cannot represent Litmus 1 because
  of `ownExcl ≤ q`; dropping that bound makes the twin's member non-coherent).

Recommendation: K now (it is also the cheapest), P held as the fallback if K's private-window agreement (§0.5 risk
R-K2) fails in the spike.

### 0.5 Risks specific to K (to be checked in a ≤ 1-day read-only spike before launch)

- **R-K1 (clock).** `tick_clock` touches `mcycle`/`mtime` and CLINT dispatch (`UTick.lean:7`); timer-pending
  (`mip.STIP`) is recomputed from `mtime` vs `stimecmp`. Extra ticks at an interrupt-DISABLED boundary change nothing
  observable before the next enabled boundary; the proofs that mention the tick (`WpTick.lean`, `WpCycle.lean`,
  `UTick.lean`, `Boot.lean:29-33`) must accept "k ticks". Expected S–M.
- **R-K2 (private window agreement).** `holding`'s long arm has frame stores (3 stack stores + `mycpu`'s frame) and a
  `lk->cpu` load; the member omits them. The padded agreement (`CertZ24.agreeW4 :80-87`) must classify them as
  SKIPPED (like failed acquires): clause 4 ("GF's writes off failed acquires are the member's") becomes "off skipped
  events", and the kill must never need a skipped private write as a chain anchor — true if no foreign hart touches a
  kernel-stack byte, which is exactly `PinTrapFrame.frameUnexemptAfter`/X1's record (rows 5/6g). If that dependency is
  judged too heavy, fallback K′: the member TAKES the long arm by reading the stale 1 whenever MachCSL's floor allows
  (it does unless an own acquire intervened since the source's co-successor was appended) and skips only otherwise —
  fewer skips, same machinery.
- **R-K3 (registers after a skipped window).** Caller-saved temporaries differ at re-convergence (`a5`, `t*`); the
  lag relation is `relT TT` (lockstep OR tainted, CertZ11/13), so this is a per-pc `decide +kernel` check that the
  caller never reads them before overwriting (acquire's `bnez a0` reads `a0`, equal on both arms).
- **R-K4 (the `started` spin).** The member exits the loop at GF's exit iteration only if its read is latest when GF's
  is: gate the `main+0x16` read on "source realized" (R43 §2) and skip GF's extra iterations.

## REQUIRED changes [R44.n] for rev 55

**[R44.1] Row 1: close at inc 16b; strike inc 19; record F44-1.** Text: "inc 15–16b DONE (MachCSL stale silent AMO,
`lvowztwx`/`vvrmlxpo`/`kwxsypop`); inc 17–18 subsumed; inc 19 (twin W4) WITHDRAWN — F44-1: a lockstep twin is not
realizable on a TSO-store log for Litmus 1/2 (R44 PART 0), independently of δ1's bound. δ1 stays (sound, faithful,
re-audited); its only remaining consumer is K′ (R-K2 fallback)." Re-size: 0 remaining. [R43.s2]'s "inc-16 bound vs
`depView`" risk is moot.

**[R44.2] New row 0 (decision) + Q-6L-SB in §D, BEFORE rows 6l/6m/19 are briefed again.** Rows 6l, 6m, 6b, 6j, 6n
depend on K vs P; the table must say "contingent on Q-6L-SB" in their dependency column. Recommended K.

**[R44.3] New row 1′ (MCSL, serial lane, after X1): the multi-tick boundary** (K only): a tick-only hart step at an
instruction boundary (or `riscvStep (k : Nat)`), `swp_tick_clock_hs` reused, `hartStep`/`MRun` arm, Vtest, the pf
twin's boundary (`pstepEv` admin step), W4 `simStep` case. 0.5–1.2k, 4–10 h, M. Spec: FAITHFUL (platform clock).

**[R44.4] Row 6l: replace R43 PART 2's text by "## Revised row 6l design" below.** Its owner-independent core
(gate record, windowed `lockCoSP` from the trace, `walkPol` from a `noStuck` premise, kill variant concluding
`cycleKillCZT` with `noStuck` NAMED) is launchable NOW (≈ 0.6–1.0k, w3's "landable now" list, confirmed). The
progress lemma `noStuck` is K-specific (skip steps are always enabled) or P-specific (landing gate).

**[R44.5] Row 6m: retire `silentQ`/`rmwQ` as named per-step premises** (false in general, 0.3); under K the datum
has no silent arm; `ordQ` for pinned reads = "source realized ⇒ the member's latest agrees with GF" (6l's gate record
+ coherence), `valQ`'s graph side per "## Q-6M-GFVAL" below (no `noPanicQ` premise — D9 [OWN.19] says panics are
not excluded, so a premise "the GF row takes no panic arm" is unsound as a header item). Re-size 6m to 1.6–3.2k
(taint walker landed 1.4k counts as done).

**[R44.6] Rows 6b/6j: "twin realization (row 1 inc 19 + twin CapF1)" → under K: the REGISTERED realization
`CapF1.recRealizedH` (`Weak/CapF1.lean:50`) on the padded member's pf run (every load latest ⇒ `scaOkT` by
`CertZ4.latestLoadFacts`; skip steps are admin steps of the record).** E1 of [R43.3] shrinks to the padded-run →
pf-run lemma (≈ 0.2–0.4k, reusing CertZ26–28's `walkRunZ4`/`pad`). Under P both rows need a buffered-store W4 (L).

**[R44.7] SCOPE (3)(ii) / §B(11): until Q-6L-SB is resolved and landed, the capstone's header carries the NAMED
`noStuck` (WEAKER) — say so explicitly; after K it is discharged (skip steps), after P by the landing-gate progress
lemma.** Also add to the risk sentence: "F44-1 (R44) — the realization target's store side".

**[R44.8] Σ and launch order.** Σ: rows 1 −2.8..−5.3k (closed) +1′ 0.5–1.2k; 6l 1.8–3.0k (K) ; 6m −0.7k; 6b/6j −0.5k
(no twin W4) ; new K-rows 6o (skip walk + padded member revival, 1.2–2.2k) and 6p (private-window agreement,
0.5–1k): net ≈ −1.5..+0.5k against rev 54's 17.7–36.9k, but confidence moves to M− across 6l/6o/6p until the spike.
Launch order: w3 → 6l core (owner-independent) now; w1 → the K spike (read-only, ≤ 1 day: R-K1..R-K4) now, then
row 1′; w2 → 6f/6h (unaffected) then 6m's remaining value lemmas. Do not brief 6b′/6j/6n before Q-6L-SB.

### Suggestions

- **[R44.s1]** Keep `Weak/Sil*` imported and green (it is the formal record that the silent twin covers exactly the
  2-hart shape); mark its headers "superseded by K (R44)". Under P they become the twin's store-buffer base instead.
- **[R44.s2]** Add Litmus 1/2 as `decide`-free Lean witnesses next to `CertZ35.crossSpinNo` (a `CertZ35`-style
  "no TSO-store log realizes Litmus 1" theorem, ≈ 0.2k) so the finding is machine-checked before the owner rules.
- **[R44.s3]** The plan's [OWN.100] text should record that (γ) as landed (silent AMO) is a PARTIAL (γ): "a non-rl AMO
  overtakes an earlier plain store" was achieved only for the AMO's own read, not for the earlier store's visibility
  to third parties.

## Revised row 6l design

### 1. Spec first

Unchanged from R43 §1: riscv.cat requires nothing of a walk order; the order is a proof device producing a member
whose log is a TSO-store order, agreeing with `GF` on labels modulo SKIPPED events (K) and on successful-protocol lock
co (`CertZ18.lockCoSP`, windowed). What F44-1 adds: the member's log MUST differ from `GF`'s gmo on W→(AMO.aq) pairs,
and the only two faithful ways to absorb that are (K) a shorter member row where `GF` observed the delayed store's
absence, or (P) a later landing. Marks: (K)/(P) FAITHFUL for the GF quantifier; (N) STRONGER; naming `noStuck` WEAKER.

### 2. The order (common core, [OWN.106]: built step by step, no acyclicity assumed)

Enabledness of a row `x` whose next GF event is `e = (x, cnt x)`:
- **fabric member**: enabled iff `e` is the next fabric member (`GF.gfDev[devCnt S] = e`) — as R43;
- **successful kernel-mode AMO on a registered lock byte** (G1 `kernelAmoAq`): enabled iff for every byte its GF
  rf-source is REALIZED and is the member's LATEST write of the byte (`srcOf GF e b = some w ∧ realizedAt S w ∧
  latestW S b = some w`); the image source (t = 0) counts as realized and latest iff no realized write;
- **GF failed acquire** (`CertZ24.lblFail`): (K) always enabled as a SKIP step (no member step; `cnt x` advances;
  `relLag` opens/extends); (P) enabled iff its source is realized, replayed silently;
- **pinned plain load** (`SilSiteTab.pinRd` ∪ the 8 device reads; under K also the two `ip->ref` sites and
  `holding+0x12`, see Q-6M-GFVAL): enabled iff its GF source is realized ([OWN.108]); (K) replayed LATEST — if the
  latest value differs from GF's and the site is `holding+0x0`/`main+0x16`/a spin read, the row enters a SKIP window
  (R-K2/R-K4); (P) replayed stale;
- **everything else**: enabled at once (loads read latest; stores append; under P a store ISSUES at once and its
  LANDING is a separate gated step: "land `w` only when every GF reader of `w`'s co-predecessor at each byte is
  realized", FIFO per hart, forced by the hart's next pw∧sr fence / same-address access).

The order is the finished trace (`SilOrd2.ordOfTrace`); the windowed `lockCoSP` comes from the GATE RECORD (every
successful kernel AMO was appended with its GF source latest), alternation at the complete member (`protRegZ`'s
`wlpAlt`, already a run-wise premise of `SilKillT.cycleKillCore :108`), CoWW (`Aᵢ <po Rᵢ`, same hart) and rf ⇒ co
(`Rᵢ →rf Aᵢ₊₁`): the window's sp writes `A₁ R₁ A₂ R₂ …` form a GF-co chain in member order (w3's "what goes through",
confirmed). `coPrefix` and Lemma 3 are DROPPED (F6l-2 is void: no "realized-but-not-latest source" case is ever
needed — a source outside the window is not gated on latest; the first in-window acquire reads the registration
zero by `regZeroAt`/E4, which IS latest at registration).

### 3. Statements (Lean sketches; new leaf `Weak/SilOrd2.lean`, imports `Weak.SilKillT` + `Weak.SilSite`; K-rows reuse
`Weak/CertZ26-30`)

```lean
/-- Gate record: hart x's n-th event was appended with its GF source latest at every byte. -/
def SilOrd2.gateRec (GF) (S : SilWalk.St) (x n : Nat) : Prop :=
  ∀ b t v, greadsByte GF.gfGd.gdG (x, n) b t v → latestAtAppend S (x, n) b t

/-- Enabledness (K form; `skip` = GF failed acquire or a private-window event). -/
inductive SilOrd2.enb (GF D Lb pin fab) (S) (cnt) (x : Nat) : Prop
  | fab   : nextIsFabric GF S cnt x → enb …
  | amo   : kernelAmo GF D Lb x (cnt x) → (∀ b, srcLatest GF S x (cnt x) b) → enb …
  | pinned: pinRdK GF D pin x (cnt x) → (∀ b, srcRealized GF S x (cnt x) b) → enb …
  | skip  : skipEv GF D Lb x (cnt x) → enb …          -- (K) always enabled
  | plain : ¬ gatedEv GF D Lb pin x (cnt x) → enb …

/-- THE DATUM at ENABLED events only (replaces `SilOrd.hartStepRIS`; (K): `CertZ29.hartStepRI4`'s shape with
`relLag` and the skip clause FREE). -/
def SilOrd2.hartStepRIS2 (d0 rows Lb GF D pin fab) (Rel : CertZ9.HRel) : Prop :=
  ∀ S x lb … , SilWalk.ok d0 S → SilOrd2.inv … S cnt → SilOrd2.enb GF D Lb pin fab S cnt x →
    (rows.getD x [])[cnt x]? = some lb →
    (skipEv … → Rel x (cnt x + 1) pE' pC) ∧                                   -- lag extends, no step
    (¬ skipEv … → ∃ lb' pa da ls' pC' w', lblReidxW lb lb' ∧ SilWalk.stepOk S x lb' none pC pa da ls' pC' d' w' ∧
        Rel x (cnt x + 1) pE' pC')

/-- LEMMA 1 (noStuck, K): while rows remain, some row is enabled. -/
theorem SilOrd2.noStuckK … : rvwmoCatAD GF.gfGd ad → gfexecConfZF boot d0 fab GF → ioResidueGmo GF → gfDevWIo GF →
    SilOrd2.kernelAmoAq boot GF → LockFacts3.diskFabPo GF → SilOrd2.inv … S cnt →
    (∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length) → ∃ x, SilOrd2.enb GF D Lb pin fab S cnt x

/-- LEMMA 2 (policy): `SilWalk.walkPol`/`CertZ26.walkPolZ4` with `noStuckK` choosing `x` and the datum at it. -/
/-- LEMMA 4 (CoAgree): at a complete walk, `CertZ8.walkOrd` ∧ windowed `CertZ23.ordCoSP` from `gateRec` +
`wlpAlt` + CoWW + rf⇒co; `CertZ30.lockCoOfOrd4` (padded member) REUSED. -/
/-- Kill: `SilKillT.cycleKillCore`'s `certSupplyS` from the K walk (padded member `CertZ27.pad` of the
twin-free candidate), `acqAqS`/`relCoversS` at padded members (CertZ25's `acqAqCZ4`/`relCoversCZ4` shapes). -/
```

Under P the `skip` constructor is replaced by `silent` (source realized) and a `land` constructor (gated landing);
`noStuckP` additionally uses: every release store is preceded by `fence rw,w` (image), so every event po-before a
pending release is gmo-before it (rule 4 with pw) — the step that makes the measure decrease through a blocked landing.

### 4. Why it is not circular

The gates read only GF's labels/rf/co, the realized prefix, and the emission datum `D` (`CertZ7.emDataOk`). Progress
(noStuck) uses cat's order axioms on UNREALIZED events' labels only: rule 5 (`acqGmoAfterC`), rf ⊆ gmo (`grfeGmo`),
co ⊆ gmo (`gwixLtGmo`), fabric ⊆ gmo (`ioResidueGmo` R3 + `gfDevWIo`), `diskFabPo`, dependency hops
(`gdepsGmo`: ctrl→W, addr) for pinned loads, rule 4 for the `started` read (`fence r,rw` after it) and (P) for
pending releases. Mutual exclusion / NF1′ / NF2a are never used at GF. Residual GF-level facts: G1 `kernelAmoAq`
(image + `kFetchText`, per pc), `diskFabPo` (device model, [R43.5]). `lockDiscCZ3`, `orderSupplyCZ3`,
`relSitesGF`/`nf1S`/`nf2S`, GF-level `oneByteS` retired as in R43.

### 5. Induction measure, progress proof sketch (K)

Measure: remaining GF events `CertZ2.rem` (skips consume events too). noStuck: suppose no row enabled; every live row's
next event is a gated AMO with an unrealized or non-latest source, a pinned load with an unrealized source, or a
fabric wait. (i) Non-latest realized source of a successful AMO `e` on byte `b`: the member's later write `w1` of `b`
was appended with ITS source latest (gate record) — `w1` is a successful AMO (reading the same source as `e`, atomicity
contradiction) or a release by the holder (then `e` reads a co-earlier value than the release while `w1`'s
holder's acquire is co-after `e`'s source: `e` is inside a window where the lock is held in GF — `e` cannot be a
SUCCESSFUL acquire reading 0; it would be `lblFail`, i.e. a skip, enabled). (ii) Unrealized source `src` (a write) on
row `h′`, next event `e′ ≤po src`: `e′ = src` is a store (enabled) or a gated AMO; `e′ <po src`: `e′` is a gated AMO
(aq ⇒ `gpos e′ < gpos src`), a pinned load (ctrl/addr/fence hop to the later store `src`, rule 9–11/4 — per-site
table, R43 R6), a skip (enabled — contradiction) or a fabric wait. `gpos` strictly decreases along the waits-for
chain; pigeonhole over ≤ `rows.length` rows. (iii) Fabric waits as R43 (the next fabric member's row has it as next
event; `diskFabPo` orders the device row). The one new case — a plain store `e′ <po src` stuck — does not exist under
K (plain stores are never gated); under P it is a pending landing, handled by the fence argument of §3.

### 6. Reuse, size, confidence, fallback

Reuse: `SilWalk.walkPol`/`walkRun` (or `CertZ26.walkPolZ4`/`walkRunZ4` for skips), `CertZ27.pad`, `CertZ28`,
`CertZ29.hartStepRI4` (datum at walk-invariant states with a FREE skip clause), `CertZ30.lockCoOfOrd4`,
`SilKillT.cycleKillCore`, `CertZ24.agreeW4`/`csChainedT4`, `acqGmoAfterC`, `grfeGmo`, `gwixLtGmo`, `CertZ8` counting
lemmas. Size (K): 6l core 0.6–1.0k (now) + noStuckK 0.5–0.8k + private-window skip (row 6p) 0.5–1k + padded-member
revival/glue to `SilKillT` (row 6o) 1.2–2.2k ⇒ **2.8–5.0k Weak, 20–40 h**; confidence M− (R-K2 is the risk); fallback
per piece: `noStuck` NAMED (WEAKER, 0), then P. Under P: 6l core as above + landing gate + noStuckP 0.8–1.4k Weak,
plus the MachCSL buffer (XL).

### 7. Row text proposed for rev 55

| 6l | **the walk ORDER, incremental with a LOCAL gate — core + progress (K)** (Weak, w3; `Weak/SilOrd2.lean`) | Gate record for successful kernel AMOs (GF source realized ∧ member-latest), pinned reads gated on "source realized" [OWN.108], GF failed acquires and private windows as SKIP steps (K), fabric in fabric order, everything else at once; order read off the trace, windowed `lockCoSP` from gate record + `wlpAlt` + CoWW + rf⇒co (no `coPrefix`, no Lemma 3); `noStuckK` from cat alone (rule 5, rf/co/fabric ⊆ gmo, per-site hops) + `diskFabPo` + G1; `orderSupplyCZ3`/`lockDiscCZ3`/GF `oneByteS` RETIRED. Contingent on Q-6L-SB = K; under P the skip arm becomes silent + gated landing. | 3′ ✓, Q-6L-SB, 6o (padded member), 6p (private windows) | 1.1–1.8k core (+6o 1.2–2.2k, +6p 0.5–1k) (fallback: `noStuck` NAMED, 0) | 8–14 (+8–18, +4–8) | M− |

## Increment 19

Neither (A) nor (C) as stated. (A) — w3 supplies `candScaTS` on the realized twin member — is FALSE: a twin member
that replays `holding+0x0` stale after an own acquire has no `scaOkT` witness at the TSO shadow (floor = log top,
`TsoShadow.shFloor :193`), and the twin's own silent bound (`ownExcl ≤ q`) already excludes Litmus 1; even a
source-position floor fails Litmus 2. (B) is WEAKER as a header and does not remove F44-1. (C) — "realized members
project to registered M2 candidates" — is unprovable for the stale-replaying twin but is EXACTLY what K delivers:
every member load reads the latest walked value, so `CertZ4.latestLoadFacts :212` gives `scaOkT` at the trace
shadow and `CertZ2.stepOkZ`'s load clause holds; skip steps are not steps of the candidate (the padded member
`CertZ27.pad` is the agreement device, the REALIZED run is the un-padded candidate), so the registered
`machRunOfPfRun` / `CapF1.recRealizedH :50` realize it with no new W4. The relation between the member's loads and
MachCSL is then the existing `viewRel`/`minViewLeSca` (W2b): the member's latest read = MachCSL's read at
`tvn = top`. Under P a twin W4 is needed again (buffer ↔ buffer, 2–3k) — another reason for K.

Decision for row 1: STOP at inc 16b (green). Increment 19 is replaced by row 1′ (multi-tick boundary) under K.

## Q-6M-GFVAL

Spec: a racy plain load may return any non-overwritten value; nothing below changes that. The worker's F9 is right that
"the graph's value `v` comes from a write the walk has not reached". The resolution is to make it NOT so: every
poisonable site whose rule has a GF side (`holding+0x0`, `holding+0x12`, `ilock+0xe`, `iunlock+0x1c`, and the PTE
rows that need custody) is GATED ON "source realized" like the pinned reads ([OWN.108]'s gate generalized). Then
`v` is the value of a REALIZED write, and the GF side of each rule follows from (i) GF's coherence at the read
(`gloadValue :300-305`: `v`'s write is co-maximal among the writes visible to the read, and the read's po-earlier own
writes are visible — CoWR), (ii) the export at the realized prefix (`lkCpuReadAt`: a non-holder never reads its own
`&cpus[x]`; `racyValOk`: every value the check can read is ≥ 1; `lockWordDiscAt`), and (iii) the member's own read of
the LATEST value `v′`, which the same export facts bound. Concretely:
- `holding+0x12` (`lkCpu`): `v` = a realized `lk->cpu` write; by (ii) `v ≠ me` unless the hart holds `lk`
  (contexts `release`/`sched`: both `= me`); `v′` likewise ⇒ `ruleOfLkCpuNe`/`Eq`. Under K in the `acquire` context
  the read sits in the long arm that the member skips when GF read a stale 1 — the rule is needed only when the
  member also took the long arm (its `lk->locked` read was 1 = latest), then (ii) applies to both.
- `ilock+0xe`/`iunlock+0x1c` (`iref`): `v ≥ 1` from (i)+(ii): GF's read cannot see below the reader's own po-earlier
  increment (CoWR), and every realized write co-after it that the check can read is ≥ 1 (`racyValOk`); `v′` the same
  ⇒ `ruleOfIrefPos`. If GF's `v` were 0 the row takes the panic arm; with the gate this cannot happen, so
  `guardsOk`'s "no panic arm" becomes a THEOREM at gated sites, not a premise. D9 [OWN.19] is respected: a GF that
  panics for another reason is still in the quantifier (the member panics too, lockstep).
- `holding+0x0` (`locked`): K — the member reads latest; if GF read a stale 1 and the member 0, the long arm is a
  skipped private window (row 6p); if both read 0 or both 1, lockstep. P — replayed stale, `vRuleRefl`.
- PTE rows: `walk+0x32`'s `V = 0 ⇒ A = D = 0` is a hardware fact about the walker's A/D updates (Svadu sets A/D only on
  valid leaves) — GF side from the walker's write-back labels (W5d-G/`WbPrimed`'s `pteAD` variant), not from values of
  unwalked writes; `walkaddr+0x1c`'s `stop` rule: replace `noPanicQ` by the custody route (Q-6M-PTE (a), from the
  realized prefix) — the premise "no block lies in `panic`" is unsound as a header item (D9).
- The census corrections (walk+0x32 path rule, walkaddr/uvmunmap return-point fixpoint) stand; `SilSiteTaint`
  (1.4k, green) is kept as the static half.
Progress cost of gating four more sites: each is a plain load whose later same-hart accesses are ordered after it by a
control dependency (`bnez`/`blez` → every later store, rule 11) or the following `amoswap.w.aq` on the same word
(`holding+0x0`, rule 1), so R43's hop table extends with no new kind of edge. Size: +0.2–0.4k on 6m (the per-site
GF-side lemmas from `gloadValue` + export), −0.3k (`noPanicQ`, `silentQ`, `rmwQ` retired). FAITHFUL (proof
organisation). Fallback: the four rules as NAMED per-site facts (WEAKER, 0).

## Owner questions the plan is missing

**Background (plain words).** The final theorem must cover every behaviour RISC-V's weak memory model (RVWMO) allows for
this xv6 binary. Our proof replays each such behaviour on a simpler machine (MachCSL) whose stores become visible to
everyone the moment they are executed, in program order ("a TSO store side"). RVWMO lets a hart's store linger in a
private buffer; in particular, the store that RELEASES a lock may still be invisible to other harts while that hart
already takes ANOTHER lock. The other harts then see the first lock as still held and spin once more. That extra spin
cannot happen on the simple machine, so the simple machine cannot replay that behaviour instruction for instruction.

**Q-6L-SB — how do we cover "a release still in the store buffer while the hart acquires another lock"?**
*Where it sits.* REMAINING WORK rows 1, 6l, 6m, 6b, 6j; `Weak/SilCand.lean:86-94` (`ownExcl ≤ q`),
`MachCSL/Lang.lean:161,209,553` (`tv := top` at an acquire); R44 PART 0.
*Terms.* *Release store*: `sw zero` to the lock word after `fence rw,w`. *Acquire*: `amoswap.w.aq` reading 0.
*Store buffer*: hardware may delay a store's global visibility; RVWMO forbids delaying it past a later store that
follows a `fence rw,w`, past a later access to the same address, or past a `.rl`, but NOT past a later acquire.
*Lockstep member*: the replay executes exactly the same instructions as the weak behaviour. *Skip*: the replay omits a
window of instructions that had no effect on anyone else (a failed spin iteration; `holding`'s longer arm).
*Clock tick*: the model advances the timer (`mtime`) at instruction boundaries; today at most once per boundary.
*Tiny example.* Hart 1: `release(b); acquire(e); acquire(d)`. Hart 2: `release(d); acquire(c); acquire(b)`. RVWMO
allows BOTH harts to see the other's lock still held (both releases linger) and spin once more each. On the simple
machine at least one of them sees the release at once. (Hart-level: hart 1's `sw zero,(b)` is in its buffer while its
`amoswap.aq (e)` performs; hart 2 reads `b` = 1.)
*Options.*
**(K) skip + multi-tick clock (recommended).** The replay omits the extra spin iteration (and `holding`'s longer arm)
and advances its clock by the omitted ticks at the next boundary, where interrupts are off anyway. An xv6 expert
reads: "the theorem covers RVWMO's buffered releases; the replay is allowed to spin less than the hardware did, and the
timer is a real clock, not an instruction counter." FAITHFUL (the real `mtime` is asynchronous; no RVWMO behaviour is
excluded). Cost: ≈ 0.5–1.2k MachCSL + 2.8–5k Weak (revives the green skip route CertZ24–33), 30–55 h; retires row 1's
twin W4 and the silent-twin realization. Risk: the private-window agreement (frame stores of `holding`'s long arm).
**(P) store buffer in MachCSL.** Give MachCSL a per-hart store buffer that acquires do not drain; keep lockstep. Reads:
"the machine IS RVWMO's store side." FAITHFUL. Cost: XL — 8–15k MachCSL (every store rule, the state interpretation,
adequacy, W4) + 3–5k Weak, serial; 2–3 months.
**(N) assume it away.** A named premise "no release lingers past the next acquire". Reads: "the theorem is about a
TSO-like machine, not RVWMO." STRONGER than RVWMO (rejected by [OWN.100]'s standard). Cost 0.
**(B) prove the needed facts in the twin logic instead of MachCSL.** Reads: "a second verification of xv6 is assumed."
WEAKER header; and it does not by itself make the twin representable (Litmus 1 fails inside the twin too). Cost ≫ 5k.

**Q-6M-GATE — may the four value-rule sites be gated on "source realized" (replayed with a realized source) instead of
carrying graph-level value premises?** *Where.* Row 6m, `Weak/SilSite.lean` `valQ`/`noPanicQ`. *Terms.* *Source
realized*: the write the weak behaviour read has already been replayed. *Value rule*: a relation between the weak read's
value and the replay's (e.g. "both ≥ 1"). *Tiny example.* `ilock` checks `ip->ref < 1` without a lock; the weak read may
return an older count; if the replay waits until that older count's write is replayed, both values come from writes
the kernel proof already constrains (≥ 1). *Options.* (a) gate (recommended): reads "every racy read is replayed from
a write the kernel proof knows about" — FAITHFUL, +0.2–0.4k, retires `noPanicQ` (which would be unsound as a header
item since panics are not excluded, D9); (b) graph-level xv6 value discipline (the census's co-interval arguments at
`GF`) — FAITHFUL but the same quantifier problem as `lockDiscCZ3`, L; (c) name the four rules — WEAKER, 0.

*Resolved without a menu.* Q-6L-REG (F6l-2): void under this design (no Lemma 3); the first in-window acquire reads
the registration zero (E4/`regZeroAt`), pre-window sources are not gated on "latest". Q-6L-PIN: [OWN.108] stands for
the gate ("source realized"); the REPLAY value is stale under P and latest-with-skip under K.

## Rev 54 table — changes from these results (summary)

| row | change |
|---|---|
| 1 | DONE at inc 16b; inc 19 WITHDRAWN (F44-1); 0 remaining [R44.1] |
| 1′ NEW | multi-tick clock boundary (MCSL, K only) 0.5–1.2k, 4–10 h, M [R44.3] |
| 0 NEW | Q-6L-SB decision gates 6l/6m/6b/6j/6n/7 [R44.2] |
| 6b, 6j | "twin realization" → registered `CapF1.recRealizedH` on the padded member's run (K); −0.3..−0.5k each [R44.6] |
| 6l | core now (0.6–1.0k, owner-independent) + noStuckK; row text §7 [R44.4] |
| 6m | retire `silentQ`/`rmwQ`/`noPanicQ`; gate the four value sites; 1.6–3.2k [R44.5] |
| 6o NEW | skip walk + padded member revived on `SilKillT` (CertZ26–30 reuse) 1.2–2.2k, 8–18 h, M− |
| 6p NEW | private-window agreement (`holding` long arm, `started` spin) 0.5–1k, 4–8 h, M− (risk R-K2) |
| 6n, 7 | consume the padded agreement (`agreeW4` already); no size change; header carries `noStuck` NAMED until 6l lands [R44.7] |
| Σ | ≈ unchanged in lines (−1.5..+0.5k), confidence M− on the K cluster until the ≤ 1-day spike; P would add 11–20k |
