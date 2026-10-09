# Theorem 2 / P4: `a3 = sext32 pid` in the post — design (advisor, 2026-10-08)

Advisory only; read-only survey of `Weak/AxWpD` (`wpdMPreStepDef`), `AxOpsem` (`astepProg`,
`awire`), `AxCert`/`AxCert2`/`AxCertP2`/`AxCertP3`/`AxDataX9` (`Cert`, `cEnd`, `bpos`),
`AxSymEngine3` (`wpdRetNode3M`, `wpdAdminNode3M`), `AxEpiChainSdLd` (`wpdOfClosedRunGM`),
`AxSymCtl` (`wpdStuckReadM`), `AxSpinE2/E4/E6` (`XBk`, `wpdInstrOfCertK`, `XxReg`, `XxSt`,
`CertBStoreS`), `AxSpinApA/ApB/T2a/T2b2/T2c5/TextCerts`, `Xv6/KernelImage.lean`,
`~/dev/weak-orch/parked/PROGRESS-AxSpinApA.md`, `notes/weak-lb-thm2-pins.md` §P4.  Sizes as
stage 2 (S ≤ 300, M ≤ 600, L ≤ 1000 lines).  Nothing here is proved.

## Verdict

**Option (1) is the one sound route, and 80 % of it already holds in the current semantics.**
The engine does not need a new "stuck-write rule": a store at `atK = LEN` IS stuck today
(no row item ⇒ no `AStepWrite`; the write node's only program step is an `LSilent` self-loop),
and the write node is a `midState`, so the `¬ midState` guard frees the post there.  What is
missing is purely LEAF machinery: (i) a register-only leaf at `k = LEN` whose row-end post may
use owned annotations, and (ii) a certificate arm that lets the evaluator STOP at a write node
(the read analogue `cEnd` exists; the write one does not).  (ii) is the only shared-engine edit
(`AxCert.Cert`, 10 one-line match sites in 6 files); `AxWpD` is untouched.
Options (2) and (3) are unsound / circular (below).  Cost M–L total (~850 lines, ~60 % copies of
existing leaves), 8 files, critical path 5 steps.  Gain remains presentational (pins note), but
the walk also closes the general "write at the row end" gap that `PROGRESS-AxSpinApA` records.

## A. What the CURRENT engine says (file:line)

1. **Post at every row-end state.**  `wpdMPreStepDef` clause (d) `⌜s.atK = LEN⌝ -∗ postLifting Φ i s`
   (AxWpD:128-131); `postLifting` (AxWp2:68) hands the post the contents of hart `i`'s whole
   annotation map `na` — resources reach the post ONLY this way, and knowing what is in `na`
   needs `annotOwn` agreement (`annotAgreeBig`, used ApA:1588).  This is why `wpdEndAnn`
   (ApA:1541) keeps `Hp` through the Löb and why its post must be state-independent (`HRQ : ∀ s`).
2. **Past `LEN` only admin steps.**  `AxSpinApA.rowEndShape` (ApA:1515): `row[k]? = none` ⇒ any
   `astepProg` is `AStepAdmin` (`lbAdmin true l`, position kept); `lbAdmin` (WeakAxRealize:130) =
   `LSilent | LDev | LRegW | LCtrl | LInstr | LIFetch`.  A fetch is an admin step pinned to the
   image (`cIf`, AxCert:168; clause (b)'s `fetchPin` premise AxWpD:117).
3. **A store at `LEN` is stuck.**  From a `memWrite` node the program steps are the store label
   (needs `AStepWrite` ⇒ a row item) or `LSilent` back to the same node: `xwritePstep`
   (AxCert2:142, exclusive polarity), `AxCert2.xwriteAstepInv` (:245); plain-store inversions
   `AxLock3Writer.astepProgPlainWriteInv` (:384), `AxSpinH4.h4WriteInv` (:158).  The node is
   `isNext` ⇒ `midState` (AxSymEngine3:286-294).  So `wpdStuckWriteM` is a 60-line mirror of
   `wpdStuckReadM` (AxSymCtl:1164-1200: `Hnord` by `row[kend]? = none`, `Hclos` by the inversion,
   `Hwire` by `awireAeqv`, post by `Hmid`).
4. **Why the evaluator cannot reach that node today.**  `Cert.cDwr` (AxCert:197) consumes a budget
   `bsucc b`; `bpos G i kk (.BFin n)` = `LEN = kk + n` (AxCert2:273) ⇒ at `kk = LEN` only
   `.BFin 0` is possible ⇒ no `cDwr`.  `cEnd` (AxCert:181) is exactly this for READS, bridged by
   `wpdStuckReadM` in `wpdOfCertK` (AxSpinE4:185-192), `wpdOfCert` (AxCert2:999), AxCertP2:157/870,
   AxCertP3:371, mono/ext lemmas AxCert:294/326/392, and a parallel inductive arm `.wEnd` in
   AxDataX9.  A `cWrEnd` arm = the same 10 sites.  `CertOfEvB` (AxCert:499) needs no arm (EvB→Cert).
5. **Register-only at `LEN` needs no engine change.**  `XBk` (AxSpinE4:375) uses `k < L` ONLY to
   refute the ret-node post obligation `Hb` by `omega` (E4:385-392); `wpdInstrOfCertK` (E4:312) is
   position-free and takes `Hb`.  `Hb` is pure (`⊢ postLifting Φ i s1`) because `wpdRetNode3M`
   (AxSymEngine3:673) states it so, but the lemma it wraps, `wpdOfClosedRunGM`
   (AxEpiChainSdLd), takes the post clause as a RESOURCE under `∧` with the continuation.  Hence
   `wpdRetNode3MR : R -∗ (R -∗ ∀ s2, RetNext → WPd s2 Φ) -∗ WPd s Φ` with
   `Hb : … → R ⊢ postLifting Φ i s1` is a ~40-line wrapper (re-derive `Hnord/Hclos/Hwire`,
   AxSymEngine3:678-697).  Mid nodes stay pure via `Hmid` (the `¬ midState` guard,
   `AxSpinE6.Hmid0` E6:131).  Wires at ret nodes are inside `wpdRetNode3M` (`RetX` modulo
   `pinReg`; GPRs preserved: `gprValAgree` AxDataX4:53, as `CertBStoreS` uses E2:905).
   `GoodB`/`GoodC` (AxSpinE:619, AxSymCtl2:189) give `rs' r = gprPost ow rs r` for `r ≠ 0`, so
   `a3` survives `jal` (`ow = (ra,·)`) and `c.addi16sp` (`ow = (sp,·)`).
6. **The three instructions (Xv6/KernelImage.lean).**  `allocproc + 0x9c` = `0x80001c0e`:
   `jal ra, 80000b7e <kalloc>` `0xf71fe0ef` (4 bytes at a 2-mod-4 address ⇒ `textAt4S`, Q22);
   `kalloc + 0` `0x80000b7e`: `c.addi sp,sp,-32` `0x1101`; `kalloc + 2` `0x80000b80`:
   `c.sdsp ra,24(sp)` `0xec06` ⇒ `va = S - 8`, 8-aligned (`S % 16 = 0`, `AxSpinApA.Lay`), inside
   `Rng` (`S - 80 ≤ a ∧ a + 8 ≤ S`, ApA:~668) and `t2Touch` (`S - 80 ≤ va < S`, T2a:1214) ⇒
   `MapOk`/`Warm` already cover the slot; fetch pages 0x80000/0x80001 are in `t2Touch`'s first
   range.  None writes `x13`.  Text instance: `AxSpinTextCerts.inText` (TextCerts:67) covers only
   `[0x80000c1e,0x80000cc8) ∪ [0x80001baa,0x80001c0c)` — NOT these; AxSpinT2c5's `σX` is the whole
   kernel text (T2c5:12) ⇒ certify there (`tailTextX` recipe, T2c5:208).
7. **Option (2) — post only at the FIRST row-end state: unsound as a theorem change.**  The
   capstone extracts the post at the run's actual final state `sN i` (`Hend`, `HfinA`,
   T2b2:355-357); `sN A` may be any of the boundaries `+0x9c`, `kalloc+0`, `kalloc+2`.  Owing the
   post only at the first would make Theorem 2 silent about the state it talks about, AND it edits
   `AxWpD` (direct importers AxLockWpD:47, AxWpDSteps:56, AxWpdLift:46 ⇒ the whole tier).  ✗.
8. **Option (3) — row items for the trailing events: circular.**  Adding `c.sdsp ra` as a row item
   moves the row end to `kalloc + 4`, another store (`c.sdsp s0` `0xe822`); ≈ 10 stores (kalloc 3,
   acquire 4, push_off 3) precede the first READ (where `cEnd` would apply), below the `S - 80`
   window ⇒ new `priv`/`Rng`/`t2Touch`, ~14 text facts, 10 `XxSt` leaves, a changed `allocFull`
   family (T2a → everything).  ✗.  A by-hand micro-step walk of `c.sdsp` (dozens of `cRd`/`cWr`
   nodes) instead of a `Cert` arm is what the evaluator exists to avoid.  ✗.

## B. Statement change

* **Post** `AxSpinApB.t2PostA GD L nm i q s :=`
  `⌜¬ midState s⌝ -∗ ⌜¬ t2CutAt (grow GD i) q i⌝ ∗ (⌜LEN = t2Len q⌝ -∗ ∃ w, ⌜pidOf GD i q =`
  `some (wbytes 4 w) ∧ npSrc … ∧ AxSpinT2a.gprOf s 13#5 = some (sext32 w)⌝ ∗ FRAG nm w)`
  (`gprOf` as T2a's original `t2Post`, T2a:669-673).  The `a3` conjunct sits under the
  complete-row guard, so the prefix-row hooks (`postP`/`hookP`/`wpdPast`, ApB:716-822) carry
  over verbatim as `postA`/`hookA`.
* **Register: `a3`, not `a0`.**  `a0` never holds the pid in the row (allocpid is inlined; the
  `mv s2,a0` at `+0xa2` is kalloc's return, unreachable — the hart stops at `kalloc + 2`).
* **Capstone** (`allocpidOpen2`, T2b2:293-361): `conclP` gains `sN` and the conjuncts
  `… → ∃ wA, pidOf A = … ∧ gprOf (sN A) 13#5 = some (sext32 wA) ∧ npSrc …` (same for B), and the
  both-complete conjunct `∃ wA wB, pidOf … ∧ gprOf (sN A) 13 = … ∧ gprOf (sN B) 13 = … ∧ wA ≠ wB`.
  Reading: whichever instruction boundary past the terminal store A stopped at, `a3` holds A's pid.
* **Premises**: + `Htxt2 : AxSpinApA.tailText2 σi T` (3 text facts: `textAt4S` at `+0x9c`,
  `textAtS` at `kalloc+0`, `kalloc+2`).  No new pins; `MapOk`/`Warm`/`Lay` unchanged (A.6).
* **Certificates**: `tailText2X` in AxSpinT2c5 (σX); the capstone-instance file passes it.
  `AxSpinTextCerts` need not change (its `inText` is the older per-function instance).

## C. File plan (sizes), DAG, risks

| # | file | content | size |
|---|---|---|---|
| F1 | `AxCert.lean` (SHARED) | `cWrEnd (d r n va req k t) : devAddr req.pa = false → akLatest = false → Cert … ⟨d, .BFin 0, r⟩ (.impure (.ok (.memWrite n va req)) k) t`; arms in the 3 mono/ext lemmas (:294/326/392) | S ~15 |
| F2 | `AxSymCtl.lean` or new `AxSymCtl6` | `wpdStuckWriteM` (mirror of `wpdStuckReadM` :1164 with a plain-write inversion) | S ~60 |
| F3 | `AxSpinE4:185`, `AxCert2:999`, `AxCertP2:157/870`, `AxCertP3:371`, `AxDataX9` (`wWrEnd` + arm) | bridge arms (copy the `cEnd` arm, call `wpdStuckWriteM`) | S, 6 × ≤ 15 |
| F4 | NEW `AxSpinE9.lean` (imports E2, E6) | `wpdRetNode3MR`, `wpdInstrOfCertKR`, `XBkEnd` (`k = L`, `e = 0`, `Hb ← R`), `XxRegEnd`; `XBVmemWriteEnd`/`XBExecuteSTOREEnd`/`CertBStoreEnd` (copies of E2:717/748/892 ending in `.cWrEnd`), `XxStEnd` (`k = LEN`, no flow, no `Out`) | M ~370 |
| F5 | NEW `AxSpinApA2.lean` (imports ApA, E9) | `tailText2`, `ap9c`/`ka0`/`ka2` + `TokC`/`textOkB` (macro ApA:191; 4-byte jal as `AxSpinAp6.atok40` on `textAt4S`), `postAOfAnnots` (the (d)-branch of `wpdEndAnn` ApA:1588-1598 factored: two annotations + pure `a3`/`pidOf`/`¬cut` ⊢ `postLifting t2PostA`), `tailA`: from the `+0x9c` boundary `XxRegEnd → XxRegEnd → XxStEnd`, each ret node via `postAOfAnnots` | S–M ~200 |
| F6 | `AxSpinApB.lean` | `t2PostA`, `postA`, `postAMid`, `hookA`; rename 24 `t2PostP` sites; replace the `wpdEnd2` closure in `segCsP` (ApB:1399-1419) by `tailA` | M ~150 changed |
| F7 | `AxSpinT2b2.lean` | `phiA`, `conclP` with `sN`, `jointP` (+ `a3` extraction), statement + `Htxt2`; 12 sites | S–M ~80 |
| F8 | `AxSpinT2c5.lean` (+ capstone instance) | `tailText2X` (3 conjuncts, `ax_t2c5_all`) | S ~15 |

**DAG**: F1 → F2 → F3 → F4 → F5 → F6 → F7; F8 after F5's definition (∥ F6).  F1–F3 are one
worker (engine lane; ONE full-tier rebuild since `AxCert` is imported by AxCert2/AxCert3/
AxDataX2/AxDataX9 and transitively the whole spin tier); F4, F5+F8, F6, F7 one worker each.
Independent of P1 except F6/F7 (ApB/T2b2); independent of Q-S2-B.

**Risks.**  (r1) Plain-write inversion polarity: `xwritePstep` is the EXCLUSIVE form
(`akLatest = true`); `wpdStuckWriteM` must use a plain-store inversion (AxLock3Writer:384 /
AxSpinH4:158 / the `pnodeStep` `memWrite` arm AxOpsem:582-590) — check the WPd-shaped one exists
or derive it (S).  (r2) AxDataX9's parallel inductive needs its own arm (unknown shape; S).
(r3) `XBkEnd`'s `bpos` at `.BFin 0`, `k = L`: `LEN = k + 0` ✓ trivial.  (r4) The jal at a
2-mod-4 address: confirm a `textOkB`-from-`textAt4S` lemma exists post-Q22 (AxSpinAp6/E7).
(r5) ApB heartbeats (`segCsP` 3.2 M, `wpdAllocpidSeg2` 6.4 M): keep the tail in F5's `tailA`
and apply it at the site, do not inline.  (r6) `GoodC` ⇒ `gprOf s' 13 = gprOf s 13` for
`ow.1 ≠ 13`: reuse ApA's sp/s1-preservation lemma through `XxReg`.  (r7) Rebuild time from F1.

## D. Owner questions (recommended first)

- **Q-P4-1 Accept the shared `AxCert` edit (`cWrEnd`)?**  (Rec) yes — the read twin `cEnd` already
  exists, the 10 sites are one-liners, and nothing sound avoids it (A.4, A.8).  Alt: skip P4.
- **Q-P4-2 Register.**  (Rec) `a3` as `gprOf (sN i) 13#5 = some (sext32 w_i)`; `a0` is never the pid.
- **Q-P4-3 Walk extent.**  (Rec) stop at `kalloc + 2` (the semantics' own stop); 3 text facts only,
  no kalloc premise.  Alt (none better).
- **Q-P4-4 Statement form.**  (Rec) `conclP GD L A B qA qB sN` with the `a3` conjunct inside the
  complete-row conjuncts.  Alt: a separate top-level conjunct in `allocpidOpen2`.
- **Q-P4-5 Placement.**  (Rec) new `AxSpinE9` / `AxSpinApA2`; edit only `AxCert` + bridges + ApB +
  T2b2.  Alt: extend E4/E6/ApA in place (bigger rebuilds, no gain).
- **Q-P4-6 Sequencing vs P1.**  (Rec) engine lane F1–F5 now (disjoint from P1); F6/F7 after P1's
  ApB/T2b2 land (both re-plumb the same two files).
