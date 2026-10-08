# Theorem 2, STAGE 2 (`allocpidOpen2`): no-panic by D4 readback on cut rows — design (advisor, 2026-10-08)

Advisory only; read-only survey of this tree (`Weak/AxSpinT2a/T2b/T2c*/T2d`, `AxSpinApA`, `AxSpinAq1/2`,
`AxSpinRl4/4b`, `AxSpinHdA/HdB/HdC`, `AxSpinPO4/5/6`, `AxWpD`, `AxWp2`, `AxSpinProt5`, `AxSpinX2`),
`notes/weak-lb-thm2-design.md` (§A, §E Q-T2-1), `notes/rocq-spinlock-plan.md` (Theorem 1, D4),
`notes/rocq-spinlock-step3-plan.md` (ID-8), `notes/weak-memory-scope.md` §2 N4/N5,
`~/dev/weak-orch/open_questions.txt` (Q-T2-1..14, Q20' Option V).  Owner ruling Q-T2-1: stage 2 proves the
NO-PANIC conjunct properly, on cut-off rows, making `t2Complete →` meaningful.  Sizes: S ≤ 300 lines,
M ≤ 600, L ≤ 1000.  Nothing here is proved.

## A. What stage 2 must prove

**Row family (new `AxSpinT2f`).**  Every row position of `allocSeg q i S p` (AxSpinT2a:223) is an
instruction boundary (items are memory events; the fence is one item; no walker items under warm TLB), so
the prefix family needs no `bnd` bookkeeping:
```
RowShP k row sh := ∀ j it, sh[j]? = some it → k + j < row.length → ∃ lb, row[k+j]? = some lb ∧ ishapeX it lb
allocPre row q i S p :=
  RowShP 0 row (allocSeg q i S p) ∧ row.length ≤ t2Len q ∧
  (value conditions of allocFull restricted to positions < row.length:
     lkBranch (t2KHd q) q.hb, spinVals, spinRmw, RowAllocpidBody, t2CpuVals, t2RelVals) ∧
  (∀ j, cutPos j q < row.length → gateOk j row q i)          -- a row past a gate took the normal arm
t2Cut GD i S p := ∃ q j, (grow GD i).length = cutPos j q ∧ ¬ gateOk j (grow GD i) q i   -- row ends at a taken off-arm
t2Complete := unchanged (AxSpinT2a:271; allocFull rows are in allocPre: lemma preOfFull)
```
The four DESIGNATED CUTS (Rocq ID-8 list, positions of this tree's shape):
| j | gate (read, row position) | off arm | cutPos |
|---|---|---|---|
| aq | acquire's holding, long arm: `ld lk->cpu` at `t2KHd q + 4` reads `cpuAddr (cpuOf i)` (hb = true only; the short arm returns 0) | `c.bnez a0,panic` taken | `t2KHd q + 12` |
| rlS | release's holding, SHORT arm: `lw lk->locked` at `t2KRh q` reads 0 (NEW: stage 1 forced `lkBranch (t2KRh q) true`) | holding returns 0, `c.beqz a0,panic` taken | `t2KRh q + 1` |
| rlL | release's holding, long arm: `ld lk->cpu` at `t2KRh q + 4` reads ≠ `cpuAddr (cpuOf i)` | `c.beqz a0,panic` taken | `t2KRh q + 12` |
| ppN | pop_off's `lw noff` at `t2KPp q + 6` with `noff < 1` | `bge` taken → panic | `t2KPp q + 7` |
| ppI | pop_off's `lw intena` at `t2KPp q + 8` (arm `q.c = false`) reads ≠ 0 | `beqz` falls → `intr_on` (csrsi; leaves the SIE = 0 regime — not a panic, but an off-path exit; Rocq: "the intr_on arm is a cut too, also refuted") | `t2KPp q + 9` |
Three are panics; `ppI` is the regime exit.  Name the conclusion `¬ t2Cut` and say in the header which arm is
which (`entersPanic := t2Cut restricted to aq/rlS/rlL/ppN`).  A row that has a flipped gate AND continues past
the cut is OUTSIDE the family (the real hart would be in `panic()`; the WPd could neither follow it nor prove it
stuck, N4) — that is what the `cutPos < length → gateOk` conjunct excludes.  Cuts inside the spin loop (B
spinning after `j < n` failed RMWs) and inside the 64-read scan are ordinary prefixes.

**Statement (`allocpidOpen2`, new `AxSpinT2b2`).**  Premises as `allocpidOpen` (AxSpinT2b:251-306) with
`HfullA/B` → `HpreA : allocPre (grow A) qA A (Sf A) (pf A)` (same for B), `HpinsA/B : AllocPins2` (below), and
ONE new image premise `Himgnoff : ∀ i ∈ [A,B], 0 ≤ noffImg (cpuOf i) ∧ noffImg (cpuOf i) < 2^31 − 1`
(`cpus[cpuOf i].noff`'s image word; pop_off's `noff < 1` check reads `noff_img + 1`, so the premise is exactly
what keeps `bge` from firing — honest and xv6-true, noff ∈ {0,1,2} at allocproc).  `HwpC`, `Hrun`, `Hend`,
`HfinA/B` unchanged.  Conclusion:
```
(∀ i ∈ [A,B], ¬ t2Cut GD i (Sf i) (pf i)) ∧
(∀ i ∈ [A,B], t2Complete GD i (Sf i) (pf i) → npSrc GD.gdG L (i, t2KBd q_i) (i, t2KA q_i)) ∧
(t2Complete A → t2Complete B → pidOf A qA ≠ pidOf B qB ∧ ∃ wA wB, pidOf A = wbytes 4 wA ∧ pidOf B = wbytes 4 wB ∧ wA ≠ wB)
```
(`npSrc` becomes conditional: a prefix ending before `t2KBd` has no nextpid read.)  Per-hart post (ID-8 shape):
`Φ i s := ⌜¬ midState s⌝ -∗ ⌜¬ t2Cut GD i⌝ ∗ (⌜t2Complete GD i⌝ -∗ ∃ w, ⌜pidOf = wbytes 4 w ∧ npSrc⌝ ∗ FRAG nm w)`
— `t2PostS` (AxSpinApA:1650) with the pure cut conjunct; `t2JointS`/`fragNe` unchanged.  `allocpid2Distinct2`
= the empty-row-C corollary as before (Q-T2-11).

**Pins that DISAPPEAR (`AllocPins` fields, AxSpinT2a:538):** `hdArm` (acquire's holding arm), `rhArm` and
`rhCpu` (release's holding lk->cpu read = this cpu), `ppGe` (noff ≥ 1), `ppInt` (intena = 0 on the `c = false`
arm); and the `allocFull` conjunct `lkBranch row (t2KRh q) true` (release's lock bit) becomes the `rlS` cut.
Each is DERIVED on the normal arm and REFUTED on the cut arm by D4 readback (§B).

**Pins that REMAIN, and why:**
- Option V return reloads `poMy1 poMy2 poMy3 poRet hdRets aqMy aqRet rhRets ppMy ppRet rlRet` and s1 reloads
  `poS1 hdS1 aqS1 rhS1 rlS1`: the reload's value is known only as an `RLfact` ANNOTATION (AxSpinE5:227), a WPd
  cannot branch on an annotation mid-row (facts surface at `postLifting`/gates only), and under Stage C a
  diverted `c.ret` into image text is NOT stuck (scope N4, Q20').  Their discharge is Rocq's ROW-INTEGRITY
  theorem (induction on prefix length via readback + prefix closure) — a separate lane, not stage 2.  Stage 2 can
  cheaply add ownership-backed VALUE INTEGRITY to the conclusion instead (§D Q-S2-4).
- Q18b `npNowrap`, `npNcoll`: scope pins (owner Q-T2-5; a verified C may drive nextpid to 1000).
- Selectors `poArm`, `ppArm` (they choose `q.b`, `q.c`; with `Himgnoff` both are determined by the image noff,
  `q.c = ¬ q.b`, but keeping them costs nothing).
- Store-data conditions `t2CpuVals`, `t2RelVals`, `spinRmw`'s data, `lkBranch (t2KHd q) q.hb`, `spinVals`: code-
  fixed data / path selectors, graph-true on real rows (AxSpinT2b header).
- GUARD every remaining pin by position: stage 1's `graphValue GD (i,k) = some (stBytes 8 …)` is FALSE at an
  absent position (`graphValue = none`); `AllocPins2` states each as `k < (grow GD i).length → …`.

## B. Feasibility under Stage C + Option V

**D4 readback works in the Lean engine; the hook already exists.**  The WPd step clause has the row-end
conjunct `⌜s.atK = LEN⌝ -∗ postLifting Φ i s` (`wpdMPreStepDef`, AxWpD:103-128, clause (d)); `postLifting`
(AxWp2:68) hands the hart's OWN annotations to the post.  `AxSpinApA.wpdEndAnn` (AxSpinApA:1541; two-annotation
form `wpdEnd2`, :1604) is the Lean form of ID-8's `HΨend` + `wpd_bnd`: at `k0 ≥ LEN`, for EVERY program state,
`WPd ⟨pr, k0⟩ Φ` from a map of own annotations and `HRQ : ∀ s, [∗map] R ⊢ Φ s` (Löb over admin steps and wires;
a store at `k ≥ LEN` has no row item so `astepProg` is not enabled — no stuck-write arm needed; this is why
Q-T2-14's missing Cert arms do NOT block stage 2).  For a cut: `HRQ` = `⌜fact⌝ ⊢ Φ s` closed by a Lean-level
contradiction between the fact and the flipped graph value (`iintro %h; exact absurd …`).  Non-cut ends:
`postLiftingTrue` (AxWp2:92) since `Φ` is pure-true there (`¬ t2Cut` from the family + LEN; `complete` false
when LEN < t2Len).  `¬ midState` final states: `postSMid` pattern (AxSpinApA:1668).  Bridges: `annotAgreeBig`
(AxWp:631), `AxSpinProt7.readbackBig`, `wpdAnnotEntail` (AxSpinH5:121).

**What each cut reads back (deposit, where it is in hand, what is NEW):**
- `rlL`: `OOwn` (AxSpinHdB:335-340: ⌜∀ j a t b, clb[j]? = a → greadsByte (i,kr) a t b → wbytes 8 val [j]? = b⌝,
  val = acquire's `mycpuRet tp`) from `FldMCpuOwn` (HdB:345) inside `holdingFromRelease'` (HdC:328) — in hand in
  Rl4's `wpdRelHead` at the `c.beqz`.  Taken arm ⇒ `ldRes 8 vcpu ≠ mycpuRet tp` vs bytes = `wbytes 8 (mycpuRet
  tp)` ⇒ False.  New: the `graphValue (i,kr) = some vcpu` ↔ `greadsByte` bridge (as `readbackBig` uses), S.
- `rlS`: holder's lock-word read via `OHeld`/`FldMLkheld` deposits ⌜≠ 0⌝; taken arm has value 0.  New:
  `holdingFromRelease'` is stated at `RowHolding … true` only (HdC:332) — generalize to `hb` or add
  `holdingFromReleaseShort` on `wpdHolding` (HdA; generic in `hb`, `KShort` at `k+1`) + `XLkOf`: S–M.
- `aq`: `ORacy` deposit ⌜rdFact (clb L) cvx G (i, aqKp+4)⌝ (HdB:240; AxSpinProt5:147: per byte, image ∨ write `w`
  with (`w.1 ≠ r.1 ∧ cpuOk`: value 0 or `cvx w.1`, Prot5:135) ∨ (`w.1 = r.1 ∧ gvisible w r`)) — in hand in Aq2's
  `mid`/`liBnez` (handed by `holdingFromAcquire'`; Aq2 drops it later, "affine").  Refutation of `= cvx i`:
  image ⇒ 0 (`Himgc`), `cpuAddr ≠ 0`; other hart `j`: `cvx j = cvx i` ⇒ `cpuAddr_inj` + `cpuOfNat` (T2LayHyp
  `nd`/`ncpu`; `Hharts` excludes a fourth writer) ⇒ `j = i`, contradiction; own write: i's lk->cpu writes are at
  `aqKm+4` and release's (`AxSpinApA.segWr`/`clbBetween`-style position facts), po-AFTER the read ⇒ `gpo w r`
  false and `gmoLt w r` false by `ppo1Gmo` (AxSpinX2:81) + asymmetry.  NEW and load-bearing: `rdFact` is PER
  BYTE; a numeric argument fails (cpus = 0x80012530, stride 128: `cvx 2` = byte 0 of `cvx 0` + byte 1 of
  `cvx 3`), so prove `clbSameSrc`: for full-class writes (`wval Cl`), `gloadValue`'s latest clause
  (WeakRvwmoGraph:238-243, `∀ w' v', gwritesByte w' a v' → gvisible w' e → gwix w' ≤ t`) forces one source
  timestamp for all 8 bytes.  S (~80 lines), pure graph lemma.
- `ppN`: pop_off's noff load (PO5, leaf `fld4`, AxSpinPO1:112) must run the PRIVATE READ flow `fxPrivRead`
  (AxSpinX2:913: deposits ⌜value = b⌝ where `w`, writing `b`, is the read's po-latest own store — a ROW fact) with
  `w` = push_off's noff store, whose data is pure in `wpdPushOff`'s continuation (`stBytes 4 (addiw1 (ldRes vn))`,
  AxSpinPO4:188); push_off's own noff load `vn` reads the image (`fxPrivRead0`/`privReadImg`, X2:177; no earlier
  noff write in the row: `segWr`).  So `noff_pop = noff_img + 1` and `bge 0 ≥ noff` is false iff `Himgnoff`.
  VERIFY FIRST that PO5 uses `fxPrivRead` (not a value-agnostic flow) — if not, switch the leaf (S).  Position
  fact "push_off's store is the po-latest noff store before pop_off's load": from `AxSpinApA.segWr` (§3-5), S.
- `ppI`: `q.c = false` ⇒ `noff_img + 1 − 1 = 0` ⇒ `noff_img = 0` ⇒ `q.b = true` (`poArm`) ⇒ push_off stored
  `intena := iena sstatus = 0` (`ienaZero`, PO1:123, under `ctrlOkSW` SIE = 0; check PO4's continuation exposes
  the intena store's data — else expose it, S) ⇒ pop_off's intena read deposit ⌜value = 0⌝ ⇒ the `beqz` is taken.

**Prefix tolerance is the real cost: NO leaf handles "row ends here".**  `XxReg` takes `k < LEN` (AxSpinE6:146),
`XxSt` `k + 1 ≤ LEN` (:184), `XxRet` `k < LEN` (:307), `wpdSpinAq` `aqKm … < LEN` (AxSpinAq1:507); every
composition DERIVES these from a full shape (`.length` sites: PO4 8, PO5 5, PO6 15, Hd9 4, HdC 3, E8 7, Aq1 6,
Aq2 15, Ap9 10, Rl4 2, Rl4b 2, ApA 13).  Q-T2-14's finding is confirmed and irrelevant: the Cert engine
(`XBk`, `cEnd`-only) is bypassed by `wpdEndAnn`.  Mechanism per row position `k` in a composition:
`by_cases hk : k < LEN`; else-branch `exact wpdEndAnn … (LEN ≤ k) … (HΨend k …)`.  Hook premise, threaded through
every CPS lemma (callees cannot know the caller's `Ψ` at a row end):
```
HΨend : ∀ k', (k' ∉ designated cuts ∨ gate not flipped) → LEN ≤ k' → ∀ pr, ⊢ wpdM … ⟨pr, k'⟩ Ψ
```
resource-free (Theorem 2's `Ψ` is pure-true at non-designated ends; instantiate by `wpdEndAnn ∅` +
`postLiftingTrue`).  The designated arms are proved LOCALLY at the four branch sites where the deposits are in
hand (no `Kpanic_j` threading).  The P-form is the SAME script with one `by_cases` per row position; since a full
row never hits the else-branch (`RowSh ⇒ RowShP` + the length), the stage-1 lemmas are corollaries — modify IN
PLACE (keep names; add `…2` where the statement changes) rather than twin 8k lines.  Loops: one generic site in
`wpdSpinAq`'s induction (Aq1) and in Ap9's scan induction.

**The prefix-closure caveat is NOT cheaply provable.**  It needs a truncation on `GdexecT` (gmo/rf/deps
restriction) preserving `rvwmoCatConsistentT`, `ctrlClosed` and the other harts' premises when no surviving
read sources a dropped write (rf-downward closure), and a REAL panicking execution continues into `panic()` →
`printf` → UART MMIO, which the graph tier excludes (N6, `devAddr = false`) — so the family's "cut before
panic's first memory event" is intrinsic, not a shortcut.  Keep it informal in the header (as Rocq, R6) and make
conjunct 1 NON-VACUOUS instead with certificate (p-lk) (§C): a protocol-violating C makes A take the panic branch,
so `HwpC` is refuted through conjunct 1.  A formal prefix-closure theorem belongs to the row-integrity lane (L).

## C. Proof architecture and work plan

| file | content | est. | size |
|---|---|---|---|
| `AxSpinT2f` (new) | `RowShP`, `allocPre`, `cutPos`/`gateOk`/`t2Cut`/`entersPanic`, `AllocPins2` (guarded), `preOfFull`, `cutNotFull`, `notCutOfLen` (pure `¬ t2Cut` at non-designated LEN), `Himgnoff` form, `RowShP` ⇐ `RowShX` | 350 | M |
| `AxSpinT2g` (new) | pure graph side of D4: `clbSameSrc`, `racyNotMine` (rdFact + Himgc + layout + position facts ⇒ `ldRes 8 v ≠ cpuAddr (cpuOf i)`), `ownIsMine` (OOwn bytes ⇒ value), `noffPop` (= img + 1), `intenaZero`, graphValue/greadsByte bridge | 400 | M |
| `AxSpinT2h` (new) | the five designated arms as `annotations -∗ ⌜LEN = cutPos⌝ → ∀ pr, WPd ⟨pr, cutPos⟩ Ψ` via `wpdEndAnn`: `cutAq`, `cutRelS` (+ `holdingFromReleaseShort`), `cutRelL`, `cutPpN`, `cutPpI` | 450 | M |
| `AxSpinPO4` (edit) | `wpdPushOff` P-form: hook, 8 sites | +120 | S |
| `AxSpinE8` (edit) | `wpdMycpu` P-form: hook, 7 sites | +100 | S |
| `AxSpinPO5`/`PO6` (edit) | pop_off P-form: hook, 20 sites, `ppN`/`ppI` arms call `AxSpinT2h` (or take them as premises `Kpp` to avoid the import cycle: T2h imports Rl/Aq? — make T2h depend only on HdB/PO1/X2, so PO5/6 can import it) | +300 | M |
| `AxSpinHd9`/`HdA`/`HdC` (edit) | holding P-form (both call sites), hook; `holdingFromRelease'` generalized to `hb` | +350 | M |
| `AxSpinAq1` (edit) | `wpdSpinAq` P-form: hook in the induction (1 generic site) | +120 | S |
| `AxSpinAq2` (edit) | `wpdAcquire` P-form, 15 sites, `aq` arm at `liBnez` (ORacy in hand) | +400 | L |
| `AxSpinRl4`/`Rl4b` (edit) | release P-form, `rlS`/`rlL` arms at the `c.beqz` (OOwn/OHeld in hand) | +350 | M |
| `AxSpinAp9` (edit) | `wpdAllocpidCs` P-form, scan induction site | +250 | M |
| `AxSpinApA` (edit/new `ApB`) | `wpdAllocpidSeg2` on `allocPre` with post `Φ2` (= `t2PostS` + `⌜¬ t2Cut⌝`), `segWr` facts restated on prefixes, `hypXv6` on `AllocPins2`/`Himgnoff` | 700 | L |
| `AxSpinT2b2` (new) | `allocpidOpen2`, `allocpid2Distinct2`, header (pins removed/kept verbatim; `Himgnoff`; informal closure caveat) | 500 | M |
| `AxSpinT2c6` (new) | (a′) re-applied: full literal rows ∈ `allocPre`, `AllocPins2` by the checkers, conclusion with both complete and `¬ t2Cut` | 200 | S |
| `AxSpinT2e1` (new) | (a-) PREFIX WITNESS: serial-then-concurrent tracer run — A to the middle of the critical section (after `sw nextpid`), B to the boundary after one failed `amoswap.w.aq` (B's row = `take (t2KSp+1) …` with `spinVals` j = 0 failing); literal rows, `graphOfSc`, premises by `preB`/`pins2B`; conclusion: `¬ t2Cut` both, `complete` false, `npSrc A` not claimed (A incomplete) — or run A to completion (then `complete A` and `npSrc A` are exercised) | 450 + compute | M |
| `AxSpinT2e2` (new) | (p-lk) NO-PANIC NEGATIVE CERTIFICATE: C = hand node `sd cvx A, 0(&lk->cpu)` (as T2d's racer, `Pexv6 hp`), interleaving C then A; A's row = the `aq` cut row (holding's long arm, lk->cpu read = `cvx A`, `length = t2KHd+12`, ≈ 20 events — the tracer memory starts after C's store; `rowsFixed` style), B phantom (empty row = `take 0`, 0 steps).  Every A/B premise holds (verbatim checkers) ⇒ by `allocpidOpen2` `¬ t2Cut A` ⇒ contradiction ⇒ `HwpC` unprovable at `protXv6` (reductio, `AxSpinT2d` template) | 400 + small compute | M |
| `AxSpinT2e3` (new) | (p-triv) sanity twin: the same C provable at `trivOb` (`ur3WpdTrivial`/`wpdRcTriv` template) | 150 | S |

DAG: `T2f ∥ T2g` (start now, no deps); `PO4 ∥ E8` → `PO5/6 ∥ Hd9/HdA/HdC` → `Aq1 → Aq2`; `Rl4 → Rl4b` (after Hd*);
`Ap9` (after T2f); `T2h ← T2g ∧ HdC`; `ApA/ApB ← Aq2 ∧ Rl4b ∧ Ap9 ∧ T2h ∧ T2f`; `T2b2 ← ApA`; certificates:
compute halves of `T2e1`/`T2e2` ← `T2f` (early), discharge ← `T2b2`; `T2c6 ← T2b2`.
**Parallel lanes (Opus, one file each, own workspace):** F (T2f → T2h), G (T2g), P (PO4 → PO5/6), H (E8 → Hd*),
A (Aq1 → Aq2; needs P, H), R (Rl4 → Rl4b; needs H), C (Ap9), L (tracer runs for T2e1/T2e2), then ApA, then
T2b2 ∥ T2e-discharge ∥ T2c6.  **Critical path:** E8 → Hd* → Aq2 → ApA → T2b2 → T2e2 (6 files, ≈ 2.5k lines).
Totals ≈ 3k new + ≈ 2k edited lines.
**Acceptance:** (i) `T2c6` type-checks with `allocpidOpen2` APPLIED on (a′) (both `¬ t2Cut`, both complete,
`wA ≠ wB`); (ii) `T2e1` applies it with B INCOMPLETE (the prefix family is exercised); (iii) `T2e2` + `T2e3`
present (the protocol, not the framework, refuses the lk->cpu racer; conjunct 1 is load-bearing); (iv) grep:
`hdArm|rhArm|rhCpu|ppGe|ppInt` absent from `AllocPins2`, `lkBranch .* (t2KRh` absent from `allocPre`; the
capstone's only iProp hypothesis is `HwpC`; (v) stage-1 `allocpidOpen`/`T2c*`/`T2d` still build (corollaries or
headers marked SUPERSEDED); (vi) `tools/ci/audit.sh --weak` roots gain `allocpidOpen2`, `allocpidRaceUnprovable`-
style roots for `T2e2`; (vii) heartbeats: Aq2/ApA may need a split at a seam (as Rl4/Rl4b).

## D. Risks and owner questions (recommended option first)

- **Q-S2-1 P-form in place vs P-twins.**  (Rec) modify the compositions IN PLACE (one `by_cases` per row
  position, hook premise `HΨend`), full-row lemmas kept as corollaries under their names; touches 11 merged
  files but avoids duplicating ≈ 8k lines.  Alt: ID-8 twins (`…P` names) — no risk to stage-1 importers,
  double the maintenance.
- **Q-S2-2 Hook shape.**  (Rec) resource-free `HΨend` for non-designated ends + the five arms proved locally
  where the deposits are in hand (`AxSpinT2h`).  Alt: Rocq's `Kpanic_j` continuations threaded through every
  callee (more plumbing, same proof).
- **Q-S2-3 New image premise `Himgnoff`.**  (Rec) accept as a named scope premise (xv6 invariant `noff ∈
  {0,1,2}` at allocproc; INT_MAX would really panic).  Alt: keep `ppGe` as a pin (then `ppN` is not a theorem).
- **Q-S2-4 Reload pins stay (Option V).**  (Rec) state it; add the ownership-backed VALUE-INTEGRITY conjunct
  `∀ reload k, graphValue (i,k) = its spill's data` to the conclusion by reading back the `RLfact` annotations
  at the row end — requires KEEPING those annotations through `KAcq`/`KRel`/`KSeg` (they are currently dropped
  as affine; M) — as the stretch of this stage.  The pins' removal is the row-integrity lane (weeks; needs
  prefix closure).
- **Q-S2-5 `intr_on` arm.**  (Rec) designated cut `ppI`, refuted; conclusion names it separately from the three
  panics.  Alt: keep `ppInt` as a pin.
- **Q-S2-6 Prefix closure.**  (Rec) informal in the header + (p-lk) makes conjunct 1 non-vacuous; formal
  truncation theorem later with row-integrity (L, model-level; MMIO past panic is outside the tier anyway).
- **Q-S2-7 Certificates.**  (Rec) (a-) prefix witness + (p-lk)/(p-triv) negative pair (A's cut row is ≈ 20
  events — cheap; the big (a′) run is only re-plumbed in `T2c6`).  Alt: (a-) only (Rocq's list) — then no
  certificate shows ownership is load-bearing for conjunct 1.
- **Q-S2-8 Q18b pins unchanged** (Q-T2-5); collision-retry family remains the alternative.
- **Q-S2-9 Release's short arm.**  (Rec) generalize `holdingFromRelease'` to `hb` (HdC) — the short arm is
  `wpdHolding`'s `KShort` with `OHeld`'s lock-word leaf.  Alt: a separate `holdingFromReleaseShort`.
- **Risk — byte mixing (`clbSameSrc`).**  If `gloadValue`'s latest clause does not yield one source for the 8
  bytes (e.g. a partial lk->cpu write licensed somewhere), the `aq` refutation needs a stronger protocol fact;
  check `protXv6`'s clb class admits 8-byte stores only (AxSpinX "lk->cpu 8 B").  S to prove, M if not.
- **Risk — PO5's noff flow.**  If the noff/intena loads are value-agnostic, no deposit exists: switch to
  `fxPrivRead` (S), verify before lane P starts.
- **Risk — guarded pins.**  Unguarded `graphValue … = some …` pins are false on prefixes; `AllocPins2` must guard
  by position or the family is empty below the pinned positions.
- **Risk — heartbeats.**  Each `by_cases` doubles the branch count in Aq2/ApA; else-branches are one-liners
  but the elaborator still sees them; plan seams as Rl4/Rl4b.
- **Risk — tracer for (p-lk).**  A's run must start from memory where C's store is already applied while the
  GRAPH image keeps `lk->cpu = 0` (`Himgc`) with C's store as the rf source; `graphOfSc`'s interleaving (C first)
  gives exactly that — confirm `rowsFixed`-style provenance works with a hand-node hart (T2d's `rcRun` pattern).
