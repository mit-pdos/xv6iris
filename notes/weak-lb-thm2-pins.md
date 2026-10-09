# Theorem 2: REDUCE PINS — design (advisor, 2026-10-08)

Advisory only; read-only survey of `Weak/AxSpinT2b2` (header pin list), `AxSpinT2f` (family, cuts,
`AllocPins2`), `AxSpinT2h` (cut arms, `wpdEnd1`/`wpdEnd2P`), `AxSpinE5/E6/E8` (reload leaf, `RLfact`),
`AxSpinPO4/PO6/HdA/Aq2/Rl4b` (pin sites), `AxSpinAp/Ap9` (allocpid code, scan), `AxSpinRl2/Rl3/Aq1`
(store-value conditions), `AxSpinX/X2` (`RNp`, `fxNpIncr`), `AxSpinApA/ApB` (posts, `Hyp2`),
`notes/weak-lb-thm2-stage2.md` §A/§D, `~/dev/weak-orch/open_questions.txt` (Q-T2-5/9'/13/14, Q18b,
Q20', Q-S2-B).  Sizes as stage 2: S ≤ 300 lines, M ≤ 600, L ≤ 1000.  Nothing here is proved.

## Summary table

| pin | remove? | mechanism | gain | cost | Q-S2-B dep |
|---|---|---|---|---|---|
| P1 reload pins (16) | YES | reload GATES + local D4 readback (`cutReload`), same engine as the five panic cuts | real: pins → `¬ t2Cut` conjunct; stack ownership becomes load-bearing for control flow | L as a lane (~1k lines, 12 files, each S–M) | avoid T2h/T2g; sequence ApB/T2b2 after |
| P2a `npNowrap` `≠ 1000` | NO (genuine scope) | wrap breaks the monotone ghost `RNp`; a "pids in use" ghost = re-verifying wrap | — | L+ | none |
| P2b `npNowrap` `+1 < 2³²` | yes, cosmetic | `RNp` invariant `v ≤ 1000` (+ `≠ 1000`) | none real | S (shared `AxSpinX`) | none |
| P2c `npNcoll` | possible, two routes | (i) collision-retry row family; (ii) derive "no collision" from ownership | (i) none real (collisions are unreachable without wrap); (ii) honest theorem | (i) L; (ii) L+, protocol change | none |
| P3 store-value conditions | possible, cosmetic | positional store flow (`FstAt`) so the leaf specialises the flow to the known data | none real (code-fixed data) | M–L, engine + 3 leaves + callers | none |
| P4 `a3` in the post | possible | row-end register walk (`XxRegEnd`, stuck-write rule) | presentational (owner skipped the tie) | M–L, engine | none |

Recommended ORDER: **P1** (only item with real gain) → P2b folded in if the shared edit is welcome →
stop.  P2c/P3/P4 only on explicit owner demand (P2c route (ii) is the one with content).

## P1. Return-address and s1 reload pins (Option V, Q20', Q-T2-13, Q-S2-4)

**What a pin is today.**  The reload leaf `XxLd` (AxSpinE6:219) pins the read to the graph value
(`graphValue (i,k) = some vs`, pure) and hands the continuation the ANNOTATION
`annotOwn (i,k) ⌜RLfact GT i pa k vw⌝` (E6:239; `RLfact` E5:227 = "the reload's bytes are the
spill's bytes `vw`").  `vw` is pure in every site (`stBytes 8 (gprVal rs0 r1)` E8:37 of the
statement, HdA:170-178, Aq2:1757-1761, PO4:236-242, Rl4b analog).  The c.ret / lock-word leaves need
the VALUE, so each site takes `Hval : graphValue (i,kr) = some (stBytes 8 ret)` (E8 wpdMycpuP:336-380,
used at :600 and :612) — the 11 ra pins + 5 s1 pins of `AllocPins2` (T2f:596-).  Q-S2-4's option
("keep the annotations through `KAcq`/`KRel`/`KSeg`, read them back at the row end") is the wrong
shape: it costs M of plumbing (ApA:79 drops them as affine) and yields a conjunct that merely
restates the premise while the pins stay.

**Mechanism (recommended): the reload is a GATE, exactly like the five panic cuts.**
* `T2Cj` (T2f:~215) gains the 16 reload cuts (or one constructor `.rl : Fin 16`); `cutPos = kr + 1`
  (the row ends right after the reload); `t2GateOk .rl_x row q i := ∀ vs, rv row kr = some vs →
  vs = expected` (for `aqS1`/`rlS1`: `expected` = the spill's own label data, `rv row 2`; the gate
  is a ROW predicate as `spinValsP`).  `allocPre`'s last conjunct (`∀ j, cutPos j q < LEN →
  t2GateOk j`) then says: a row that CONTINUES past a reload read the spilled value.  The pins
  leave `AllocPins2` (only `poArm`/`ppArm`/`npNowrap`/`npNcoll` remain).  `cutPosLen/Ord/Inj/Ge`
  (T2f:244-270) are re-proved; 21 cuts make the pairwise `cases j <;> cases j'` 441 `omega`s —
  prefer injectivity via a position list.
* Callee restatement, per site (E8, PO4, HdA/Hd9, Aq2, PO6, Rl4b — ~9 code sites): replace
  `Hval` by the GUARDED form `Hgate : graphValue (i,kr) ≠ some vw → LEN ≤ kr + 1` (implied by the
  old pin, so the stage-1/2 statements remain corollaries); at the boundary `kr + 1`, pure
  `by_cases` on the value: equal ⇒ today's script; else `Hgate` gives `LEN ≤ kr + 1` and the arm is
  `AxSpinT2h.wpdEnd1 … (kr+1) … (i,kr) ⌜RLfact …⌝ Ψ HRQ` (T2h:397) with the annotation from the
  leaf, `HRQ : RLfact → ∀ s, ⊢ Ψ s` closed by contradiction: `RLfact` + `graphValue (i,kr) = some vs`
  + the bridge `AxSpinT2h.ldOfRd`/`ldEq` (T2h:104-150: graph value ↔ `greadsByte`) ⇒ `vs = vw`.  One
  GENERIC lemma `cutReload (kr) (pa) (vw) : annotOwn (i,kr) ⌜RLfact⌝ -∗ ⌜graphValue (i,kr) = some vs⌝
  → vs ≠ vw → LEN ≤ kr+1 → ∀ pr, WPd ⟨pr,kr+1⟩ Ψ` (no `Ψ` knowledge needed — the arm is refuted,
  not proved) serves all 16 sites.  E8: `ret` must become `gprVal rs0 r1` (the pin was the only
  link between the reload and `ret`; the callers know `ra` from the jal — T2a's `jalrRets`), and
  `Hret : jalrTgt 0 ret = ret` stays.
* ApB: 16 one-line "gate ⇒ `Hgate`" bridges from `allocPre`; `notCutAt` (ApB:577) gains the reload
  positions (each discharged by the normal-arm value in hand); `Hyp2` (ApB:~600) shrinks.  T2b2:
  header pin list, `¬ t2Cut` now also covers "a reload read a value other than its spill".
* Certificates: `T2q1/q2/q3`, `T2c6` replace the `AllocPins2` checkers by gate checkers on literal
  rows (`decide`, −/±).  NEW cheap negative certificate (p-stk): C = hand node storing to A's `ra`
  spill slot — refused by `protXv6` (stack window private, `WOK`), the row-integrity analogue of
  (p-lk) `AxSpinT2e2`: ownership of the stack is what keeps the control flow on the row.

**Gain (honest).**  Premises lose 16 pins; conclusion gains: no covered execution has a reload that
reads anything but its spill (hence no diverted `c.ret`, no wrong lock address).  Coverage: rows
ending at `kr + 1` with a wrong value are now REFUTED instead of excluded.  Rows with a wrong value
that CONTINUE are still outside the family — the same informal prefix-closure caveat as the panic
cuts (T2b2 header "Prefix closure"), but cleaner here: truncating the execution right after the
wrong reload needs no MMIO argument, only the graph truncation lemma on `GdexecT` (the
row-integrity lane, L, model level; nothing reload-specific remains).  Nothing about C changes.

**Cost.**  T2f +150 (S), new `AxSpinT2i` (`cutReload`, bridges) +120 (S) — NOT in T2h (Q-S2-B edits
T2h/T2g), E8 +60, PO4 +80, HdA/Hd9 +120, Aq2 +120 (heartbeat risk: 2273 lines — the else-branches
are one-liners; keep the seam), PO6 +80, Rl4b +100, ApB +180 (M), T2b2 +60, certs ±100, (p-stk)
+300 + small compute.  ≈ 1k–1.2k lines, 12 files; each file S–M.  **Parallel:** T2f ∥ T2i first
(fix the `Hgate` shape in a 20-line stub before the leaf lanes start); then E8 ∥ PO4 ∥ HdA ∥ Aq2 ∥
PO6 ∥ Rl4b (each independent given the stub); then ApB → T2b2 → certs.  **Q-S2-B:** no shared file
if `cutReload` lives in T2i; ApB/T2b2/T2h-dependent certificates land after the rework merges.

## P2. Q18b scope pins (`npNowrap`, `npNcoll`)

**Code (AxSpinAp:13-40).**  The retry path (`beq a4,a3 → +0x5c; c.mv a3,a1; c.mv a1,a0 (=1);
beq a3,a6 (pid=1000 keeps next=1); addiw a1,a3,1; a5 = proc; rescan`) does NOT re-read nextpid: the
candidate advances in registers (`pid+1`, or `1` after `1000`) and the 64-slot scan restarts.

**P2a `≠ 1000` — keep (genuine scope).**  `RNp` (AxSpinX:606) is a monotone counter (`MonoNat` auth,
issued set `S` below `v`); `fxNpIncr` (X2:1048) mints ◯{v} and writes `v+1`; distinctness is
`issuedFragExcl`.  A wrap writes `1`: the counter goes DOWN and distinctness across a wrap is
genuinely a property of the scan, not of the counter.  Removing the pin = a new ghost ("pids in
use", the scan's reads become ownership-backed) — re-verifying allocpid's wrap semantics: L+.
Rename to what it is (`npNoWrap1000`) and keep it in the header as the ONE scope premise.

**P2b `toNat + 1 < 2³²` — derivable, cosmetic.**  Strengthen `RNp` with `v ≤ 1000` (xv6Init: image
nextpid = 1; `fxNpIncr` requires `v ≠ 1000` which the pin gives) ⇒ `v + 1 < 2³²`.  S, but edits the
shared protocol file `AxSpinX` + `xv6Init` + `fxNpIncr`'s `Hdata` shape (X2:1055); do only as a
rider on another protocol edit.  Nothing real is gained.

**P2c `npNcoll` — two routes, both L; neither covers a new real execution.**
HONESTY first: in a covered graph the scan reads return the image (`proc[].pid = 0`, candidate
≥ 1) or A's/B's own `p->pid` store (issued earlier, `< ` the reader's counter value); other `proc[]`
slots are BLOCKED for everyone (`xlayXv6`, `WOK`).  So without wrap a collision is unreachable —
the pin excludes no xv6 execution, it only looks like a scope restriction.
* Route (i) collision-retry family (mechanical).  `T2Prm` gains `js : List (Fin 64)` (collision
  index of each aborted scan; the last scan is full); body length `1 + Σ(j_t+1) + 64 + 2`; the
  scan values become PATH SELECTORS in `allocPre` (as `spinValsP`: read `≠` candidate before `j_t`,
  `=` at `j_t`) — Q18a's value-agnostic `FldMWScan` reads stay; candidate = `v + |js|`, nextpid
  write = `v + |js| + 1`, `npNowrap` becomes "no intermediate candidate = 1000".  Needs
  `fxNpIncrD` (X2: mint ◯{v+d}, write `v+d+1`; the `S < v` invariant is monotone-safe: S, new
  lemma beside the old), Ap9's `scanLoopP` generalised to a retry induction (new `Ap9b`, L: the
  +0x5c/+0x60/+0x62 certs exist, AxSpinAp:192-196), T2a/T2f positions (`t2KA`, `kEqs`, `nDet`-style
  `jsDet`: M), ApA/ApB body call site (M), T2b2 (S), certs (`js = []` must reduce to today's
  checkers; a collision WITNESS needs a tracer run from a memory with `proc[j].pid = 1`: M).
  ≈ 1.3k lines, 8 files.  Gain: the premise disappears; the family grows by unreachable rows.
* Route (ii) derive "no collision" (content, but protocol change).  Make the scan reads deposit
  "value ∈ image ∪ {pids issued below the reader's counter}": a protocol on `proc[].pid` bytes for
  OTHER slots (today private-class per owner, Q-T2-4; blocked otherwise), plus `RNp` carrying the
  issued set's relation to the stored pids, plus hb from the lock (A's `p->pid` store is lob-before
  B's acquire).  Conclusion gains "no retry happens"; Q18a's value-agnostic ruling is partly undone.
  L+, touches `AxSpinX/X2/Ap8/Ap9/ApB`.  Only worth it if the owner wants the theorem to SAY that
  collisions are impossible before wrap.

## P3. Store-value row conditions (`t2CpuVals`, `t2RelVals`, `spinRmwP`'s data; Q-T2-9')

**Why they exist.**  `FstM` (AxSymMem, via `XBk`'s store bridge) quantifies over EVERY row position:
`FstMCpu` (Rl2:318-330, deviation 2 Rl2:60-70), `FstRel` (Rl3:54, `Hst`), `fstAcqNh` (Aq1:71) must
be legal flows at every future store position after their anchor, and `fxCpuWrite`/`fxReleasePid`/
the RMW flow only have arms for data `cvx i`/`0`, `z4`, the swap word.  The WPd learns a store's
data only when the store executes (`XxStF` Ap8:396 — continuation gets `graphData = wbytes n val`,
`val` the register), too late for a flow demanded at anchor time.  `XxSdCpu` (Rl2:414) and
`XxSwRel` (Rl3:319) are value-generic and derive nothing about the data themselves.

**Derivation route.**  A POSITIONAL store flow (`FstAt k data`, the `DKSt` twin of AxCertP3's windowed
`FldMW`, Rl2's own alternative "windowed store bridge, M"): the leaf consumes the flow obligation
INSIDE the step where `graphData (i,k) = some (stBytes n (gprVal rs rs2))` is pinned, so the caller
proves the flow only for the actual data (`cpuAddr (cpuOf i)` from mycpu, `x0`, the swap word).
Then `t2CpuVals`/`t2RelVals`/`spinRmwP`'s data leave `allocPre`; `CpuWin` (Rl2:201) keeps only its
position/lob half.  Engine (`XxStF`/`XBk` bridge) M, rewire Rl2/Rl3/Aq1 S each, cascade into
Aq2/Rl4/Rl4b/ApB (every `cpuWinP`/`relZ4` site: ApB:676, :1072-1527) M.  Total M–L, ~8 files.

**Gain (honest): cosmetic.**  The data is fixed by the code (`cvx i` from mycpu's return, `x0`,
`a0 = 1`); a row with other data is not generated by this program, so no real execution is added;
the premises merely stop naming data that the leaves could compute.  `lkBranch (t2KHd q) q.hb`,
`spinValsP`, `bodyIds` are path selectors / identities and are not pins at all.  Recommend: skip;
if the owner wants `allocPre` to be "shape + selectors only", do it after P1 (shares no files with
P1 except ApB; none with Q-S2-B).

## P4. The `a3` register fact (Q-T2-14)

**Why it is missing.**  `wpdMPreStepDef`'s clause (d) (AxWpD:128) demands the post at EVERY state
with `atK = LEN`; past `+0x9a` the hart runs `jal kalloc`, kalloc's `c.addi sp`, then `c.sdsp ra`
(a store with no row item: `astepProg` not enabled ⇒ stuck, MaybeStuck) (ApA:45-56).  `wpdEndAnn`
(ApA:1541) proves the row-end WPd for ALL states (`HRQ : ∀ s, …`), so the post must be
state-independent (`t2PostS`/`t2PostP`).  None of these instructions writes `a3`, so
`a3 = sext32 w` is TRUE at every reachable row-end state; the engine just cannot walk them.

**Mechanism.**  (1) `XxRegEnd`: at `k ≥ LEN`, a register-only instruction with its `CertC`/`TokC`
decode (the `XBk` machinery without the `k < LEN` bound): `WPd ⟨s,k⟩ Φ ⇐ postLifting Φ s ∧ (∀ s'
successor, WPd ⟨s',k⟩ Φ)`; (2) `wpdStuckWrite`: at `k ≥ LEN` with a store at `PC`, clauses (a)/(b)
vacuous, so `WPd ⇐ postLifting Φ s ∧ wires`; (3) the wire clause (c): `awire` (AxOpsem:714) changes
device pins only — the walk must be stated modulo pins (wpdEndAnn's Löb template, ApA:1552);
(4) text premise for `+0x9c` and kalloc's first two words (`tailText2`, as `AxSpinApA.tailText`
ApA:186); (5) post `⌜¬ midState s⌝ -∗ ⌜a3 = sext32 w⌝ ∗ t2PostP` in ApA/ApB (`KSeg` already carries
`a3` at the boundary, ApA:925-1191), T2b2 conclusion, certificates re-plumbed.  Engine 400–600 +
ApA/ApB 150 + T2b2 60 + certs: M–L.  Risk: Löb over admin steps with a non-constant `Φ`; the
reachable-state characterisation is new ground (nothing in the tree walks past `LEN`).

**Gain (honest): presentational.**  The owner ruled "conclusion over `pidOf`, tie theorem skipped";
`pidOf` (the stored pid word) already identifies the issued pid.  Recommend: skip.  Zero-cost
alternative if a register statement is wanted in the header: cite `AxSpinApA.wpdAllocpidSeg`'s
`KSeg` (`a3 = sext32 w` at `PC = allocproc + 0x9c`) as the boundary fact, as ApA already does.

## Order, parallelism, dependencies

1. **P1 now** (value/cost best; the only real coverage change).  Week-scale lane: T2f ∥ T2i stub →
   six leaf lanes in parallel → ApB → T2b2 → certs + (p-stk).  Start the leaf lanes while Q-S2-B is
   in flight (disjoint files); hold ApB/T2b2 until the rework lands (they import T2h).
2. **P2b** as a rider if `AxSpinX` is being edited anyway (Q-S2-B touches protXv6): S, cosmetic.
3. **P2c (ii)** only on demand; **P2c (i)**, **P3**, **P4**: not recommended (cost without real gain).
   P3 and P4 are independent of P1 and of each other except ApB/T2b2; none depends on Q-S2-B.

## Owner questions (recommended first)

- **Q-P1-1 Reload cuts vs value-integrity conjunct.**  (Rec) treat each reload as a designated cut at
  `kr + 1` (gate = "read the spill"), remove the 16 pins, extend `¬ t2Cut`; the discharge is local
  (`cutReload` via `wpdEnd1`), no annotation plumbing.  Alt: Q-S2-4's row-end readback conjunct
  (M of plumbing, pins stay — not recommended).
- **Q-P1-2 `wpdMycpu`'s `ret`.**  (Rec) restate as `gprVal rs0 r1` (callers know `ra` from the jal);
  keep `Hret`.  Alt: keep `ret` abstract plus a premise `gprVal rs0 r1 = ret`.
- **Q-P1-3 Where `cutReload` lives.**  (Rec) new `AxSpinT2i` (no Q-S2-B conflict).  Alt: T2h after
  the rework merges.
- **Q-P1-4 (p-stk) certificate.**  (Rec) yes — ownership of the stack shown load-bearing for control
  flow, T2e2 template.  Alt: skip (then P1's conjunct has no negative witness).
- **Q-P2-1 `≠ 1000`.**  (Rec) keep as the one named scope premise, renamed; wrap = L+ (new ghost).
- **Q-P2-2 `npNcoll`.**  (Rec) keep; header states that collisions are unreachable without wrap (image
  pids 0, own pids below the counter, other slots blocked).  Alt (i) retry family L; alt (ii)
  derive via a `proc[].pid` protocol, L+ (partly undoes Q18a).
- **Q-P3 / Q-P4.**  (Rec) skip both; document as "code-fixed data" / "boundary fact in `KSeg`".
