/-
Weak: **THEOREM 2, STAGE 2 (`allocpidOpen2`) and THEOREM 1 (`allocpid2Distinct2`)** — the two-hart
allocpid capstones on xv6's REAL `allocproc` (inlined allocpid, `allocproc + 0x38 .. + 0x9a`) with
the NO-PANIC conjunct PROVED on PREFIX (cut-off) rows by D4 readback (owner ruling Q-T2-1, stage 2).
Stage-2 design `notes/weak-lb-thm2-stage2.md` §A (statement), §C row `AxSpinT2b2`.  NEW Lean file
(no Rocq source: the Rocq development stopped before the capstone; Rocq's ID-8 is the model).
The stage-1 capstones `allocpidOpen` / `allocpid2Distinct` (AxSpinT2b) are untouched.

## What this file proves

**`allocpidOpen2`** (Theorem 2, stage 2, OPEN THIRD HART).  Harts A and B run the inlined allocpid
segment from `allocproc + 0x38` (`entryOk`) on rows of the PREFIX family `allocPre` (AxSpinT2f: a
row may stop anywhere — inside the spin loop, the scan, at a designated cut — as long as a row that
continues past a gate — panic or reload — took the normal arm), with the pins `AllocPins2`; hart C is ARBITRARY,
constrained ONLY by the iProp premise `HwpC`.  Conclusion, with `GD = gtAdGd GT`:
```
  (∀ i, i ∈ [A, B] → ¬ t2Cut GD i (Sf i) (pf i)) ∧                                  -- NO PANIC
  (t2Complete GD A (Sf A) (pf A) → npSrc GD.gdG L (A, t2KBd qA) (A, t2KA qA)) ∧
  (t2Complete GD B (Sf B) (pf B) → npSrc GD.gdG L (B, t2KBd qB) (B, t2KA qB)) ∧
  (t2Complete A → t2Complete B → pidOf GD A qA ≠ pidOf GD B qB ∧
     ∃ wA wB, pidOf GD A qA = some (wbytes 4 wA) ∧ pidOf GD B qB = some (wbytes 4 wB) ∧ wA ≠ wB)
```
`t2Cut GD i S p` (AxSpinT2f) = hart `i`'s row is a family row that ENDS at a designated cut whose
gate read took the OFF arm: `aq` (acquire's holding, long arm, `lk->cpu` = this cpu ⇒ panic),
`rlS` (release's holding reads `lk->locked` = 0 ⇒ panic), `rlL` (release's holding reads
`lk->cpu` ≠ this cpu ⇒ panic), `ppN` (pop_off's `noff < 1` ⇒ panic) — these four are
`entersPanic` — and `ppI` (pop_off's `intena ≠ 0` on the `c = false` arm ⇒ `intr_on`, an off-path
exit from the SIE = 0 regime, not a panic) — OR (P1, owner ruling 2026-10-08) that ends right after
one of the 18 RELOADS (`T2Rj`: the return-address and `s1` reloads) having read a value other than
its spill (`reloadMis`).  `cutIff : t2Cut ↔ entersPanic ∨ intrOnCut ∨ reloadMis`.  `¬ t2Cut`
therefore says: neither A nor B enters `panic()` (nor `intr_on`), and NO RELOAD of A or B reads
anything but its spill (no diverted `c.ret`, no wrong lock address), on any covered execution —
the reload part currently via the INTERIM premise `AllocPins2.rlEnd` (see PINS KEPT).

**`allocpid2Distinct2`** (Theorem 1) — the corollary with C's row EMPTY (owner ruling Q-T2-11):
C is a phantom agent of the layout with `grow C = []`, empty run, `HwpC` by `AxSpinT2b.wpdEmpty`.
Same conclusion.

## How

As stage 1 (`AxSpinT2b.allocpidOpen`): `tierAAdequacyAnnGateJointT` at `AxSpinX7.xv6GF`, policy
`xv6Pol GT`, `protXv6 L`, `xv6Init L`, `xv6HobAlloc L`, `xv6Hok GT HconsT Hcl`, harts `[A, B, C]`
(script `AxSpinJ2.uAllocOpen`).  `Hwp` = A's and B's `AxSpinApB.wpdAllocpidSeg2E` (post
`AxSpinApB.t2PostP`, bundle `AxSpinApB.Hyp2` from `AxSpinApB.hypXv6P`) and `HwpC`, lifted to the
per-hart post `AxSpinT2b2.phiP` by `AxSpinWit.tierAWpdMono`.  `Hjoint` = `AxSpinT2b2.jointP`: the
posts at the non-mid final states give the q-indexed cut conjuncts `¬ t2CutAt`, and on complete
rows (`LEN = t2Len q`) the stage-1 facts; `AxSpinT2a.fragNe` (issued-fragment exclusivity,
position-independent) gives `wA ≠ wB` when both are complete.  Bridges to the design's
q-free statement: `AxSpinApB.notCutOfAt` (`¬ t2CutAt row q` ⇒ `¬ t2Cut`, via `cutDet`) and
`AxSpinT2b2.qDet` (a complete row of the family fixes the parameters: `t2Complete` ⇒
`LEN = t2Len qA`, via `AxSpinT2f.qEqFull`: `bDet`/`hbDet`/`nDet`/`cDet`).

## What changed vs stage 1

PREMISES.  `HfullA`/`HfullB : allocFull …` → `HpreA`/`HpreB : allocPre …`; `HpinsA`/`HpinsB :
AllocPins` → `AllocPins2`; NEW explicit premises (each also glossed at the binder):
* `HimgNoff : HimgNoff GD.gdG.gxImg A B` — `cpus[cpuOf i].noff`'s image word `v` satisfies
  `0 ≤ v < 2^31 − 1` for `i ∈ {A, B}` (Q-S2-3, named scope premise; xv6-true: `noff ∈ {0,1,2}`
  at allocproc).  pop_off's `noff < 1` test reads `v + 1` (D4: its own push_off store), so this
  is exactly what refutes `ppN` (and, with `poArm`, `ppI`).
* NO source-alignment premise: **Q-S2-B (byte mixing) RESOLVED BY THE PROTOCOL** (owner ruling
  2026-10-08).  The `aq` refutation is per byte (`rdFact`), and without source alignment two
  writers' bytes could mix into this cpu's address.  Instead of a premise about C's writes,
  `protXv6` itself now requires every `lk->cpu` write to be full-width (σ conjunct `CLFULL`,
  AxSpinX deviation 8; xv6's writers are the 8-byte `sd`s of acquire/release), the racy read
  deposits `clSrcFull` (`AxSpinX2.fxCpuRacyS`, `ORacy`), and `AxSpinT2h.cutAq` derives
  `AxSpinT2g.clSrcAligned` from it.  The former premises `HsrcAlA`/`HsrcAlB` are GONE.
* `Himgc` (the `lk->cpu` image is 0) — unchanged from stage 1, now ALSO used by `cutAq`.
* `Hwlt` (writers of `lk->cpu` are harts `< NCPU`), required by `wpdAllocpidSeg2E`, is NOT a
  premise here: it is DERIVED from `Hharts` + `T2LayHyp.ncpu` (`AxSpinT2g.writerLt`).
Everything else (`HconsT`, `Hcl`, `Hharts`, `HLay`, `HalA/B`, `Hn0`, `Himgn`, the eight text
premises, `HfixA/B`, translation, `HmapA/B`, `HentA/B`, `HkC`, `Hrun`, `Hend`, `HfinA/B`, `HwpC`)
is verbatim stage 1.

PINS REMOVED (no longer premises; on the normal arm they follow from `allocPre`'s gate conjuncts,
at a cut they are refuted by D4 readback in AxSpinT2h's arms `cutAq`/`cutRelS`/`cutRelL`/
`cutPpNF`/`cutPpIF`):
`hdArm` (acquire's holding long arm), `rhArm` and `rhCpu` (release's holding `lk->cpu` read = this
cpu), `ppGe` (`noff ≥ 1`), `ppInt` (intena = 0 on the `c = false` arm), and `allocFull`'s
conjunct `lkBranch row (t2KRh q) true` (release's holding lock bit, now the `rlS` gate).
P1 (owner ruling 2026-10-08) ALSO REMOVED — the 18 positional RELOAD pins of the former
`AllocPins2` (Option V return-address reloads `poMy1 poMy2 poMy3 poRet hdRets(2) aqMy aqRet
rhRets(2) ppMy ppRet rlRet` and `s1` reloads `poS1 hdS1 aqS1 rhS1 rlS1`): a row that CONTINUES
past a reload read its spill by `allocPre`'s reload-gate conjunct (`∀ x, rlPos x q < LEN →
rlGateOk x row q`, AxSpinT2f §2–3); and the selector `poArm` (now `allocPre`'s `poBranch`,
`AxSpinT2f.poArmOf`).

PINS KEPT — `AllocPins2 GD i q` (AxSpinT2f §5), VERBATIM:
```
  npNowrap : ∀ vs, graphValue GD (i, t2KBd q) = some vs →
    (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32
  npNcoll : ∀ vs, graphValue GD (i, t2KBd q) = some vs → ∀ j, j < 64 → ∀ v,
    graphValue GD (i, t2KBd q + 1 + j) = some v → (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs
  ppArm : ∀ vn, graphValue GD (i, t2KPp q + 6) = some vn →
    (addiwm1 (ldRes false 4 vn) != zero_reg) = q.c
  rlEnd : ∀ x, (AxOpsem.grow GD i).length = rlPos x q → rlGateOk x (AxOpsem.grow GD i) q
```
(`LEN = (grow GD i).length`.)  Classification: Q18b scope pins `npNowrap`, `npNcoll`; the selector
`ppArm` (chooses `q.c`); and the INTERIM row-end premise `rlEnd` — "a row that ENDS right after a
reload read the spill there" (vacuous unless `LEN = rlPos x q = kr + 1`).  HONEST STATUS of the
reload reading: the leaf P-forms (AxSpinE8, PO4, HdA/Hd9, Aq2, PO6, Rl4b) still take guarded pins
`kr < LEN → graphValue (i, kr) = vw`; ApB supplies them from `allocPre`'s gate (`kr + 1 < LEN`)
and `rlEnd` (`kr + 1 = LEN`) through `AxSpinT2f.pinOf`.  So today `¬ reloadMis` (the reload part
of conjunct 1) is a consequence of `rlEnd`, not proved by readback; when the leaf lanes take
`AxSpinT2i.Gate` (from `allocPre` alone, `AxSpinT2f.gateBody`) the row end `kr + 1` is REFUTED by
`cutReload` and `rlEnd` is deleted.  The gain already in: 18 positional pins (constraining every
present reload) → one premise at the single possible row end.  The value conditions inside
`allocPre` (`t2CpuVals`, `t2RelVals`, `spinRmwP`'s data, `lkBranch (t2KHd q) q.hb`,
`spinValsP`, the body's read identities, `poBranch`) are stage 1's, restricted to present
positions: code-fixed store data and path selectors (AxSpinT2b header, verbatim there).

## Prefix closure (informal, Q-S2-6)

The family stops a row BEFORE the off arm's first event of a designated cut: a real panicking hart
continues into `panic()` → `printf` → UART MMIO, which the graph tier excludes (`devAddr = false`,
scope N6), so "the row ends at the cut" is intrinsic, not a shortcut.  That every execution's
rows are (prefixes in) the family — a truncation theorem on `GdexecT` preserving consistency, ctrl
closure and the other harts' premises — is NOT proved (it belongs to the row-integrity lane); a
row with a flipped gate that CONTINUES past the cut is outside the family by `allocPre`'s gate
conjunct.  The theorem's quantification is over family rows only.

## HONESTY: why ownership is load-bearing here

C is constrained ONLY by `HwpC`; no premise mentions C's row, values or control flow.  As in stage
1, `npSrc` and `wA ≠ wB` hold because every write C can perform is licensed by `protXv6`.  NEW at
stage 2: CONJUNCT 1 IS LOAD-BEARING.  A C that stores `cvx A` to `lk->cpu` without holding the
lock makes A's acquire-time holding read `lk->cpu` = A's cpu and A take the `aq` panic cut; the
premises of A are all satisfiable on such a graph, so `¬ t2Cut A` would be FALSE — the reductio
(certificate p-lk, design §C row `AxSpinT2e2` / AxSpinT2p2) shows that such a C's WPd is
UNPROVABLE against `protXv6` (while provable against the trivial protocol, p-triv).  The
refutation of `aq` uses the deposit's `clSrcFull` (protocol full-width lk->cpu writes, Q-S2-B) and
`Himgc`; `rlS`/`rlL` use the holder's own
deposits (`OHeld`/`OOwn`); `ppN`/`ppI` use pop_off's private reads of push_off's stores and
`HimgNoff`.

What the theorems do NOT say: anything about a row outside the family (diverted control flow or
addresses, a pinned value that differs, a nextpid of 1000 / wrapping / colliding — the Q18b pins
restrict WHICH executions are covered, they do not constrain C); `npSrc` and distinctness only for
COMPLETE rows (`t2Complete`; a prefix ending before the nextpid read has no such read).  TLB warm,
PTE pages read-only (`entryOk`, `MapOk`).  `HfinA`/`HfinB`: runs stop at instruction boundaries.
IMAGE NOTE (stage 1's): `σi` must be a text + page-table image (as `AxSpinTextCerts.σK`).

## Deviations from the design

1. The npSrc conjunct is stated per hart (`t2Complete A → npSrc … qA`, `t2Complete B → …`) rather
   than `∀ i ∈ [A, B]` — the parameters `qA`/`qB` are per hart.
2. `Hwlt` is derived (see above), not a premise (stronger than the assignment's list).
3. Post `t2PostP` is `a3`-free (stage 1's Q-T2-14 ruling, AxSpinApA FINDING).
4. Theorem 1 keeps the phantom C in the layout (stage 1 deviation 5).
5. Audit roots: `Weak.allocpidOpen2`, `Weak.allocpid2Distinct2` registered (`tools/ci/roots-weak.txt`,
   `tools/audit/baseline-weak.json`, `tools/ci/audit.sh --weak` modules / build line).

**Reused** (by name): `tierAAdequacyAnnGateJointT` (AxSpinJ), `xv6Init`/`xv6HobAlloc`/`xv6Hok`/
`xv6AxpolWf`/`protXv6`/`clb`/`npb` (AxSpinX), `AxSpinX7.xv6GF`, `xlayXv6`/`xlayXv6Ok`/`T2LayHyp`/
`entryOk`/`entryK0`/`t2Complete`/`pidOf`/`AxSpinT2a.fragNe`/`AxSpinT2a.hartLt` (AxSpinT2a),
`allocPre`/`AllocPins2`/`HimgNoff`/`t2Cut`/`t2CutAt`/`AxSpinT2f.coreOfPre`/`qEqFull`
(AxSpinT2f), `AxSpinT2g.writerLt`,
`AxSpinApB.wpdAllocpidSeg2E`/`hypXv6P`/`t2PostP`/`notCutOfAt`, `AxSpinT2b.initCs`/`distinct`/
`mem3`/`pidNe`/`over`/`overSelf`/`overNe`/`wpdEmpty`, `AxSpinJ2.bigSepLTriple`,
`AxSpinWit.tierAWpdMono`, `catTAd`, `nsteps_O`.

**Lean-only declarations**: `allocpidOpen2`, `allocpid2Distinct2` (grepped absent from the tree);
helpers `AxSpinT2b2.*`.
-/
import Weak.AxSpinApB
import Weak.AxSpinT2b

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Determinacy of the parameters on a complete row -/

/-- A COMPLETE row of the family fixes its parameters: a prefix-family row for `q` that is a
full row for `q'` has `q = q'` (push_off's arm, holding's lock bit, the spins, pop_off's arm). -/
theorem AxSpinT2b2.qDet {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) (HF : allocFull row q' i S p) : q = q' :=
  AxSpinT2f.qEqFull (AxSpinT2f.coreOfPre H) HF

/-- `t2Complete` of a family row is `LEN = t2Len q` for the row's own parameters. -/
theorem AxSpinT2b2.lenOfComplete {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p) :
    t2Complete GD i S p → (AxOpsem.grow GD i).length = t2Len q := by
  rintro ⟨q', HF⟩
  rw [AxSpinT2b2.qDet H HF]
  exact HF.2.1

/-! # 2. The joint step for `t2PostP` -/

/-- The per-hart post: A, B: `t2PostP`; anyone else: `True`. -/
def AxSpinT2b2.phiP (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) :
    InvGS_gen .hasNoLC AxSpinX7.xv6GF → AxannotGS AxSpinX7.xv6GF → Xv6N → Agent → Athread →
      IProp AxSpinX7.xv6GF :=
  fun _ _ nm i s =>
    if i = A then AxSpinApB.t2PostP GD L nm A qA s
    else if i = B then AxSpinApB.t2PostP GD L nm B qB s else iprop(True)

/-- The joint conclusion, q-indexed: no cut row; complete rows give pid + `npSrc`; both
complete give distinct words. -/
def AxSpinT2b2.conclP (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) : Prop :=
  ¬ t2CutAt (AxOpsem.grow GD A) qA A ∧ ¬ t2CutAt (AxOpsem.grow GD B) qB B ∧
  ((AxOpsem.grow GD A).length = t2Len qA → ∃ wA : BitVec 32,
    pidOf GD A qA = some (WeakInterpProj.wbytes 4 wA) ∧
      npSrc GD.gdG L (A, t2KBd qA) (A, t2KA qA)) ∧
  ((AxOpsem.grow GD B).length = t2Len qB → ∃ wB : BitVec 32,
    pidOf GD B qB = some (WeakInterpProj.wbytes 4 wB) ∧
      npSrc GD.gdG L (B, t2KBd qB) (B, t2KA qB)) ∧
  ((AxOpsem.grow GD A).length = t2Len qA → (AxOpsem.grow GD B).length = t2Len qB →
    ∃ wA wB : BitVec 32, pidOf GD A qA = some (WeakInterpProj.wbytes 4 wA) ∧
      pidOf GD B qB = some (WeakInterpProj.wbytes 4 wB) ∧ wA ≠ wB)

theorem AxSpinT2b2.phiPA (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm)
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N)
    (s : Athread) :
    AxSpinT2b2.phiP GD L A B qA qB Hinv Hann nm A s = AxSpinApB.t2PostP GD L nm A qA s := by
  simp [AxSpinT2b2.phiP]

theorem AxSpinT2b2.phiPB (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) (hAB : A ≠ B)
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N)
    (s : Athread) :
    AxSpinT2b2.phiP GD L A B qA qB Hinv Hann nm B s = AxSpinApB.t2PostP GD L nm B qB s := by
  simp [AxSpinT2b2.phiP, Ne.symm hAB]

theorem AxSpinT2b2.phiPC (GD : Gdexec) (L : Xlay) (A B C : Agent) (qA qB : T2Prm) (hCA : C ≠ A)
    (hCB : C ≠ B) (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF)
    (nm : Xv6N) (s : Athread) :
    AxSpinT2b2.phiP GD L A B qA qB Hinv Hann nm C s = iprop(True) := by
  simp [AxSpinT2b2.phiP, hCA, hCB]

/-- THE JOINT STEP: the three posts at non-mid final states give `conclP` (fragment exclusivity
`AxSpinT2a.fragNe` when both rows are complete). -/
theorem AxSpinT2b2.jointP (GD : Gdexec) (L : Xlay) (A B C : Agent) (qA qB : T2Prm)
    (sN : Agent → Athread) (hAB : A ≠ B) (hmA : ¬ midState (sN A)) (hmB : ¬ midState (sN B))
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) :
    ⊢ ([∗list] i ∈ [A, B, C], AxSpinT2b2.phiP GD L A B qA qB Hinv Hann nm i (sN i)) ==∗
      ⌜AxSpinT2b2.conclP GD L A B qA qB⌝ := by
  have Htri : ([∗list] i ∈ [A, B, C], AxSpinT2b2.phiP GD L A B qA qB Hinv Hann nm i (sN i)) ⊢
      AxSpinApB.t2PostP (GF := AxSpinX7.xv6GF) GD L nm A qA (sN A) ∗
        AxSpinApB.t2PostP (GF := AxSpinX7.xv6GF) GD L nm B qB (sN B) := by
    refine (AxSpinJ2.bigSepLTriple A B C _).1.trans ?_
    rw [AxSpinT2b2.phiPA, AxSpinT2b2.phiPB _ _ _ _ _ _ hAB]
    exact sep_mono .rfl sep_elim_left
  iintro HI
  ihave HI := Htri $$ HI
  icases HI with ⟨HPA, HPB⟩
  unfold AxSpinApB.t2PostP
  ihave HPA := HPA $$ %hmA
  ihave HPB := HPB $$ %hmB
  icases HPA with ⟨%HcA, HKA⟩
  icases HPB with ⟨%HcB, HKB⟩
  by_cases hA : (AxOpsem.grow GD A).length = t2Len qA
  · by_cases hB : (AxOpsem.grow GD B).length = t2Len qB
    · ihave HKA := HKA $$ %hA
      ihave HKB := HKB $$ %hB
      icases HKA with ⟨%wA, %HwA, FA⟩
      icases HKB with ⟨%wB, %HwB, FB⟩
      ihave %Hne := (AxSpinT2a.fragNe (GF := AxSpinX7.xv6GF) nm wA wB) $$ [FA FB]
      · isplitl [FA]
        · iexact FA
        · iexact FB
      imodintro
      ipureintro
      exact ⟨HcA, HcB, fun _ => ⟨wA, HwA⟩, fun _ => ⟨wB, HwB⟩,
        fun _ _ => ⟨wA, wB, HwA.1, HwB.1, Hne⟩⟩
    · ihave HKA := HKA $$ %hA
      icases HKA with ⟨%wA, %HwA, -⟩
      imodintro
      ipureintro
      exact ⟨HcA, HcB, fun _ => ⟨wA, HwA⟩, fun h => absurd h hB, fun _ h => absurd h hB⟩
  · by_cases hB : (AxOpsem.grow GD B).length = t2Len qB
    · ihave HKB := HKB $$ %hB
      icases HKB with ⟨%wB, %HwB, -⟩
      imodintro
      ipureintro
      exact ⟨HcA, HcB, fun h => absurd h hA, fun _ => ⟨wB, HwB⟩, fun h => absurd h hA⟩
    · imodintro
      ipureintro
      exact ⟨HcA, HcB, fun h => absurd h hA, fun h => absurd h hB, fun h => absurd h hA⟩

/-! # 3. THEOREM 2, stage 2 -/

set_option maxHeartbeats 1600000 in
/-- **THEOREM 2 (`allocpidOpen2`, stage 2: no panic by D4 readback on prefix rows).**  Harts A, B
run the inlined allocpid of xv6's `allocproc` on rows of the PREFIX family, hart C is an
ARBITRARY program verified against the joint protocol (`HwpC`, the only iProp premise).  Then
neither A nor B ends at a taken panic / `intr_on` arm or right after a misread reload
(`¬ t2Cut`; the reload part via the interim `AllocPins2.rlEnd`), complete rows' nextpid reads
are sourced by the gmo-latest nextpid write before their claim, and if both rows are complete
the stored pids are distinct.  Premises glossed one per line; the kept pins are verbatim in the
file header. -/
theorem allocpidOpen2 (GT : GdexecT) (A B C : Agent) (Sf pf : Agent → Int) (ptp : Int → Prop)
    (qA qB : T2Prm) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (n0 : Int)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    -- MODEL: the tagged graph is riscv.cat-consistent
    (HconsT : rvwmoCatConsistentT GT)
    -- MODEL: control dependencies are closed (`AxSpinGate`)
    (Hcl : ctrlClosed GT)
    -- SCOPE: only A, B, C emit memory events
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B, C])
    -- LAYOUT: distinct harts < NCPU, distinct `proc[]` slots, disjoint stack windows in `stack0`
    (HLay : T2LayHyp A B C Sf pf ptp)
    -- LAYOUT: allocproc's frames of A and B are 16-aligned
    (HalA : Sf A % 16 = 0) (HalB : Sf B % 16 = 0)
    -- IMAGE: `lk->cpu` is 0 initially (initlock); also refutes the `aq` cut's image source
    (Himgc : ∀ a, a ∈ clb (xlayXv6 A B C Sf pf ptp) → GT.gtG.gxImg a = some b0)
    -- IMAGE: nextpid's initial value `n0` is a 32-bit word
    (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    -- IMAGE: nextpid's bytes initially hold `n0`
    (Himgn : ∀ (j : Nat) a v, (npb (xlayXv6 A B C Sf pf ptp))[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    -- IMAGE (NEW, Q-S2-3): A's / B's `cpus[].noff` image word is in [0, 2^31 - 1)
    (HimgN : HimgNoff (gtAdGd GT).gdG.gxImg A B)
    -- TEXT: the kernel text of acquire, mycpu, push_off, holding, pop_off, release, allocpid's
    -- inlined copy and allocproc's + 0x98 / + 0x9a (`σi` = text + page-table image)
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    -- TEXT: A's / B's reads of `σi`'s domain return `σi`'s bytes, which are in the graph image
    (HfixA : textFixed (gtAdGd GT) A (imgS σi)) (HfixB : textFixed (gtAdGd GT) B (imgS σi))
    -- TRANSLATION: Sv39 satp, ASID 0, root = `T`
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    -- TRANSLATION: `T` maps A's / B's data ranges VA = PA (load / store / AMO)
    (HmapA : AxSpinApA.MapOk σi T A (Sf A) (pf A)) (HmapB : AxSpinApA.MapOk σi T B (Sf B) (pf B))
    -- ROWS (NEW): A's / B's rows are in the PREFIX family (may stop anywhere; past a gate —
    -- panic or reload — only on the normal arm)
    (HpreA : allocPre (AxOpsem.grow (gtAdGd GT) A) qA A (Sf A) (pf A))
    (HpreB : allocPre (AxOpsem.grow (gtAdGd GT) B) qB B (Sf B) (pf B))
    -- PINS (NEW): Q18b + `ppArm` + the interim row-end reload premise `rlEnd` (header);
    -- panic arms, the 18 reload pins and `poArm` removed
    (HpinsA : AllocPins2 (gtAdGd GT) A qA) (HpinsB : AllocPins2 (gtAdGd GT) B qB)
    -- ENTRY: A / B start at allocproc + 0x38, S-mode, SIE = 0, sp / s1 / tp set, warm TLB
    (HentA : entryOk T satp0 A (Sf A) (pf A) (s0 A))
    (HentB : entryOk T satp0 B (Sf B) (pf B) (s0 B))
    -- ENTRY: C starts at row position 0
    (HkC : (s0 C).atK = 0)
    -- RUN: each hart's run is `n i` model steps from `s0 i` to `sN i`
    (Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B, C] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    -- RUN: each hart's run consumes its whole row
    (Hend : ∀ i, i ∈ [A, B, C] → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    -- RUN: A's / B's runs stop at an instruction boundary
    (HfinA : ¬ midState (sN A)) (HfinB : ¬ midState (sN B))
    -- C: an arbitrary program verified against the joint protocol (the ONLY iProp premise)
    (HwpC : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 C) .MaybeStuck C (fun _ => iprop(True))) :
    (∀ i, i ∈ [A, B] → ¬ t2Cut (gtAdGd GT) i (Sf i) (pf i)) ∧
    (t2Complete (gtAdGd GT) A (Sf A) (pf A) →
      npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (A, t2KBd qA) (A, t2KA qA)) ∧
    (t2Complete (gtAdGd GT) B (Sf B) (pf B) →
      npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (B, t2KBd qB) (B, t2KA qB)) ∧
    (t2Complete (gtAdGd GT) A (Sf A) (pf A) → t2Complete (gtAdGd GT) B (Sf B) (pf B) →
      pidOf (gtAdGd GT) A qA ≠ pidOf (gtAdGd GT) B qB ∧
      ∃ wA wB : BitVec 32,
        pidOf (gtAdGd GT) A qA = some (WeakInterpProj.wbytes 4 wA) ∧
        pidOf (gtAdGd GT) B qB = some (WeakInterpProj.wbytes 4 wB) ∧ wA ≠ wB) := by
  obtain ⟨hAB, hAC, hBC⟩ := AxSpinT2b.distinct HLay
  have Hcons := catTAd GT HconsT
  have HL := xlayXv6Ok A B C Sf pf ptp HLay
  -- the `lk->cpu` writers are harts < NCPU (from `Hharts` and the layout)
  have Hwlt : ∀ w a v, a ∈ clb (xlayXv6 A B C Sf pf ptp) →
      gwritesByte (gtAdGd GT).gdG w a v → w.1 < NCPU := fun w a v _ hw =>
    AxSpinT2g.writerLt (gtAdGd GT).gdG Hcons.1 [A, B, C] Hharts
      (fun j hj => AxSpinT2a.hartLt A B C Sf pf ptp HLay j (AxSpinT2b.mem3 hj)) w a v hw
  have HyA := AxSpinApB.hypXv6P A B C Sf pf ptp HLay GT σi T A qA (.inl rfl) HalA HpreA HpinsA
    HimgN HmapA Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixA
  have HyB := AxSpinApB.hypXv6P A B C Sf pf ptp HLay GT σi T B qB (.inr rfl) HalB HpreB HpinsB
    HimgN HmapB Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixB
  have Hk0 : ∀ i, i ∈ [A, B, C] → (s0 i).atK = 0 := by
    intro i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · exact entryK0 T satp0 _ _ _ _ HentA
    · exact entryK0 T satp0 _ _ _ _ HentB
    · exact HkC
  have Hwp : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [A, B, C], xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [A, B, C],
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
            (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 i) .MaybeStuck i
            (AxSpinT2b2.phiP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm i) := by
    intro Hinv Hann nm
    have WA := (AxSpinApB.wpdAllocpidSeg2E (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF)
      (xlayXv6 A B C Sf pf ptp) GT nm HL Hcons σi T satp0 hmode hasid hppn A qA (Sf A) (pf A)
      HyA Himgc Hwlt (s0 A) HentA).trans (wand_mono .rfl (wand_mono .rfl
        (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 A) .MaybeStuck A _
          (AxSpinT2b2.phiP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm A)
          (fun s => by rw [AxSpinT2b2.phiPA]))))
    have WB := (AxSpinApB.wpdAllocpidSeg2E (hlc := .hasNoLC) (GF := AxSpinX7.xv6GF)
      (xlayXv6 A B C Sf pf ptp) GT nm HL Hcons σi T satp0 hmode hasid hppn B qB (Sf B) (pf B)
      HyB Himgc Hwlt (s0 B) HentB).trans (wand_mono .rfl (wand_mono .rfl
        (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 B) .MaybeStuck B _
          (AxSpinT2b2.phiP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm B)
          (fun s => by rw [AxSpinT2b2.phiPB _ _ _ _ _ _ hAB]))))
    iintro HI
    icases (AxSpinJ2.bigSepLTriple A B C
      (fun i => xv6Init (GF := AxSpinX7.xv6GF) (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm i)).1
      $$ HI with ⟨HA, HB, HC⟩
    iapply (AxSpinJ2.bigSepLTriple A B C _).2
    isplitl [HA]
    · ihave HA := AxSpinT2b.initCs (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm A $$ HA
      icases HA with ⟨Hil, Hnh⟩
      ihave W := WA $$ []
      · iempintro
      iapply W $$ Hil Hnh
    isplitl [HB]
    · ihave HB := AxSpinT2b.initCs (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm B $$ HB
      icases HB with ⟨Hil, Hnh⟩
      ihave W := WB $$ []
      · iempintro
      iapply W $$ Hil Hnh
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit
        (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (s0 C) .MaybeStuck C (fun _ => iprop(True))
        (AxSpinT2b2.phiP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB Hinv Hann nm C)
        (fun s => by rw [AxSpinT2b2.phiPC _ _ _ _ _ _ _ (Ne.symm hAC) (Ne.symm hBC)]))
      iapply HwpC nm $$ HC
  have Hjoint : ∀ [Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF] [Hann : AxannotGS AxSpinX7.xv6GF]
      (nm : Xv6N),
      ⊢ ([∗list] i ∈ [A, B, C], AxSpinT2b2.phiP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB
          Hinv Hann nm i (sN i)) ==∗
        ⌜AxSpinT2b2.conclP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB⌝ := by
    intro Hinv Hann nm
    exact AxSpinT2b2.jointP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B C qA qB sN hAB HfinA HfinB
      Hinv Hann nm
  have HP := @tierAAdequacyAnnGateJointT AxSpinX7.xv6GF _ _ (xv6Pol GT) GT Xv6N Unit
    (protXv6 (xlayXv6 A B C Sf pf ptp)) (xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT))
    (xv6AxpolWf GT) HconsT [A, B, C] HLay.nd Hharts s0 sN n Hrun Hk0 Hend
    (AxSpinT2b2.phiP (gtAdGd GT) (xlayXv6 A B C Sf pf ptp) A B qA qB) Hwp _ Hjoint
    (xv6HobAlloc (GF := AxSpinX7.xv6GF) (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) n0 HL Himgc Hn0
      Himgn)
    (xv6Hok GT HconsT Hcl)
  obtain ⟨HcA, HcB, HnA, HnB, Hd⟩ := HP
  refine ⟨?_, fun h => (HnA (AxSpinT2b2.lenOfComplete HpreA h)).choose_spec.2,
    fun h => (HnB (AxSpinT2b2.lenOfComplete HpreB h)).choose_spec.2, fun hA hB => ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact AxSpinApB.notCutOfAt HpreA HcA
    · exact AxSpinApB.notCutOfAt HpreB HcB
  · obtain ⟨wA, wB, HpA, HpB, Hne⟩ :=
      Hd (AxSpinT2b2.lenOfComplete HpreA hA) (AxSpinT2b2.lenOfComplete HpreB hB)
    exact ⟨AxSpinT2b.pidNe _ _ wA wB HpA HpB Hne, wA, wB, HpA, HpB, Hne⟩

/-! # 4. THEOREM 1, the corollary with an empty-row C -/

set_option maxHeartbeats 800000 in
/-- **THEOREM 1 (`allocpid2Distinct2`, stage 2)** — two harts A, B run the inlined allocpid on
prefix-family rows; nobody else emits events.  The corollary of `allocpidOpen2` with a phantom
third hart C whose row is empty (its run is empty, its `HwpC` is `AxSpinT2b.wpdEmpty`).  Same
premises as Theorem 2 minus C's, same conclusion. -/
theorem allocpid2Distinct2 (GT : GdexecT) (A B C : Agent) (Sf pf : Agent → Int)
    (ptp : Int → Prop) (qA qB : T2Prm) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (n0 : Int)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    -- MODEL: the tagged graph is riscv.cat-consistent
    (HconsT : rvwmoCatConsistentT GT)
    -- MODEL: control dependencies are closed
    (Hcl : ctrlClosed GT)
    -- SCOPE: only A and B emit memory events
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B])
    -- SCOPE: the phantom third hart C of the layout has an empty row
    (HrowC : AxOpsem.grow (gtAdGd GT) C = [])
    -- LAYOUT: as Theorem 2 (C's slot / stack window are reserved, never used)
    (HLay : T2LayHyp A B C Sf pf ptp)
    (HalA : Sf A % 16 = 0) (HalB : Sf B % 16 = 0)
    -- IMAGE: `lk->cpu` = 0, nextpid = `n0`, the noff image words (as Theorem 2)
    (Himgc : ∀ a, a ∈ clb (xlayXv6 A B C Sf pf ptp) → GT.gtG.gxImg a = some b0)
    (Hn0 : 0 ≤ n0 ∧ n0 < 2 ^ 32)
    (Himgn : ∀ (j : Nat) a v, (npb (xlayXv6 A B C Sf pf ptp))[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GT.gtG.gxImg a = some v)
    (HimgN : HimgNoff (gtAdGd GT).gdG.gxImg A B)
    -- TEXT: as Theorem 2
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    (HfixA : textFixed (gtAdGd GT) A (imgS σi)) (HfixB : textFixed (gtAdGd GT) B (imgS σi))
    -- TRANSLATION: as Theorem 2
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (HmapA : AxSpinApA.MapOk σi T A (Sf A) (pf A)) (HmapB : AxSpinApA.MapOk σi T B (Sf B) (pf B))
    -- ROWS and PINS: as Theorem 2 (prefix family, kept pins; verbatim in the header)
    (HpreA : allocPre (AxOpsem.grow (gtAdGd GT) A) qA A (Sf A) (pf A))
    (HpreB : allocPre (AxOpsem.grow (gtAdGd GT) B) qB B (Sf B) (pf B))
    (HpinsA : AllocPins2 (gtAdGd GT) A qA) (HpinsB : AllocPins2 (gtAdGd GT) B qB)
    -- ENTRY: as Theorem 2
    (HentA : entryOk T satp0 A (Sf A) (pf A) (s0 A))
    (HentB : entryOk T satp0 B (Sf B) (pf B) (s0 B))
    -- RUN: A's and B's runs, whole rows, stopped at instruction boundaries
    (Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
    (Hend : ∀ i, i ∈ [A, B] → (sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length)
    (HfinA : ¬ midState (sN A)) (HfinB : ¬ midState (sN B)) :
    (∀ i, i ∈ [A, B] → ¬ t2Cut (gtAdGd GT) i (Sf i) (pf i)) ∧
    (t2Complete (gtAdGd GT) A (Sf A) (pf A) →
      npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (A, t2KBd qA) (A, t2KA qA)) ∧
    (t2Complete (gtAdGd GT) B (Sf B) (pf B) →
      npSrc (gtAdGd GT).gdG (xlayXv6 A B C Sf pf ptp) (B, t2KBd qB) (B, t2KA qB)) ∧
    (t2Complete (gtAdGd GT) A (Sf A) (pf A) → t2Complete (gtAdGd GT) B (Sf B) (pf B) →
      pidOf (gtAdGd GT) A qA ≠ pidOf (gtAdGd GT) B qB ∧
      ∃ wA wB : BitVec 32,
        pidOf (gtAdGd GT) A qA = some (WeakInterpProj.wbytes 4 wA) ∧
        pidOf (gtAdGd GT) B qB = some (WeakInterpProj.wbytes 4 wB) ∧ wA ≠ wB) := by
  obtain ⟨hAB, hAC, hBC⟩ := AxSpinT2b.distinct HLay
  -- C's (empty) run: it starts and ends at position 0 and takes no step
  let sC : Athread := ⟨(s0 A).atP, 0⟩
  have Hharts3 : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [A, B, C] := by
    intro e He
    have h := Hharts e He
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  have Hrun3 : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [A, B, C] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinT2b.over C 0 n i) (AxSpinT2b.over C sC s0 i)
        (AxSpinT2b.over C sC sN i) := by
    intro Hann nm i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [AxSpinT2b.overNe _ _ _ _ hAC, AxSpinT2b.overNe _ _ _ _ hAC,
        AxSpinT2b.overNe _ _ _ _ hAC]
      exact Hrun Hann nm _ (by simp)
    · rw [AxSpinT2b.overNe _ _ _ _ hBC, AxSpinT2b.overNe _ _ _ _ hBC,
        AxSpinT2b.overNe _ _ _ _ hBC]
      exact Hrun Hann nm _ (by simp)
    · rw [AxSpinT2b.overSelf, AxSpinT2b.overSelf, AxSpinT2b.overSelf]
      exact nsteps_O _
  have Hend3 : ∀ i, i ∈ [A, B, C] →
      (AxSpinT2b.over C sC sN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [AxSpinT2b.overNe _ _ _ _ hAC]
      exact Hend _ (by simp)
    · rw [AxSpinT2b.overNe _ _ _ _ hBC]
      exact Hend _ (by simp)
    · rw [AxSpinT2b.overSelf, HrowC]
      rfl
  have HwpC : ∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
      ⊢ xv6Init (xlayXv6 A B C Sf pf ptp) (gtAdGd GT) nm C -∗
        @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol GT) (gtAdGd GT) Xv6N Unit
          (protXv6 (xlayXv6 A B C Sf pf ptp)) nm (AxSpinT2b.over C sC s0 C) .MaybeStuck C
          (fun _ => iprop(True)) := by
    intro Hinv Hann nm
    rw [AxSpinT2b.overSelf]
    exact AxSpinT2b.wpdEmpty (xlayXv6 A B C Sf pf ptp) GT nm C HrowC (s0 A).atP _
  exact allocpidOpen2 GT A B C Sf pf ptp qA qB σi T satp0 n0 (AxSpinT2b.over C sC s0)
    (AxSpinT2b.over C sC sN) (AxSpinT2b.over C 0 n) HconsT Hcl Hharts3 HLay HalA HalB Himgc Hn0
    Himgn HimgN Htxa Htxm Htxp Htxh Htxq Htxr Htxc Htxt HfixA HfixB hmode hasid hppn HmapA HmapB
    HpreA HpreB HpinsA HpinsB
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HentA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HentB)
    (by rw [AxSpinT2b.overSelf])
    Hrun3 Hend3
    (by rw [AxSpinT2b.overNe _ _ _ _ hAC]; exact HfinA)
    (by rw [AxSpinT2b.overNe _ _ _ _ hBC]; exact HfinB)
    HwpC

end Weak
