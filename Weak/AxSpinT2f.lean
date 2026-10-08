/-
Weak: **THEOREM 2, STAGE 2 — THE PREFIX ROW FAMILY** (pure): the cut-off rows `allocPre` of the
inlined allocpid segment, the five DESIGNATED CUTS (`cutPos`, `t2GateOk`, `t2Cut`,
`entersPanic`), the GUARDED pins `AllocPins2`, the noff image premise form `noffImgOk`, and the
bridges from stage 1.  Stage-2 design `notes/weak-lb-thm2-stage2.md` §A (spec) and §C row
`AxSpinT2f`.  NEW Lean file (no Rocq source; Rocq's ID-8 prefix family is the model).

## What this file provides (the interface for AxSpinT2h, the Ap9/ApA P-forms, T2b2, T2e*)

§1 PREFIX SHAPES over `Rxitem`.  `RowShXP k row sh` (the `Rxitem` twin of AxSpinRowP's
   `RowShP`): every item whose row position `k + j` is PRESENT is matched (`xshape`); lemmas
   `rowShXPOfX` (`RowShX ⇒ RowShXP`), `rowShXOfXP` (full length ⇒ `RowShX`), `rowShXPAppL/AppR`,
   `rowShXPMap` (`↔ RowShP` of the `Ritem` list), `rowShXPCongr`; `AxSpinT2f.segPartsP` = stage 1's
   `AxSpinT2a.segParts` on prefixes (each piece of `allocSeg` as `RowShP`/`RowShXP` at its
   position).  Every row position is an instruction boundary (Stage C: items are memory events,
   the fence is one item, no fetch / walker items under the warm TLB), so no `bnd` bookkeeping.
§2 THE DESIGNATED CUTS.  `T2Cj` = `aq | rlS | rlL | ppN | ppI`; `cutPos j q` (the row length at
   which the off arm's first event would be the next item) and `t2GateOk j row q i` (the gate
   read took the NORMAL arm; vacuous when the read is absent):
   | j     | gate read (position)                       | normal arm (`t2GateOk`)            | `cutPos`      |
   | `aq`  | acquire's holding `ld lk->cpu` `t2KHd q+4` | `hb → value ≠ cpuAddr (cpuOf i)`    | `t2KHd q+12`  |
   | `rlS` | release's holding `lw lk->locked` `t2KRh q`| value `≠ 0` (long arm)              | `t2KRh q+1`   |
   | `rlL` | release's holding `ld lk->cpu` `t2KRh q+4` | value `= cpuAddr (cpuOf i)`         | `t2KRh q+12`  |
   | `ppN` | pop_off's `lw noff` `t2KPp q+6`            | `bge zero,noff` falls (`noff ≥ 1`)  | `t2KPp q+7`   |
   | `ppI` | pop_off's `lw intena` `t2KPp q+8`          | `c = false → intena = 0`            | `t2KPp q+9`   |
   `aq`, `rlS`, `rlL`, `ppN` are the PANIC arms (`entersPanic`); `ppI` is the `intr_on` arm, an
   off-path exit from the SIE = 0 regime (not a panic; Rocq: "the intr_on arm is a cut too").
   Positions: `AxSpinT2f.cutPosLen` (`cutPos j q < t2Len q`), strictly increasing in `j`
   (`AxSpinT2f.cutPosOrd`), `AxSpinT2f.cutPosInj`; `AxSpinT2f.kEqs` = every segment position
   in terms of `t2KHd`, `holdLen`, `n`, `ppLen`.  T2h / ApA tell DESIGNATED from non-designated
   row ends by `∃ j, LEN = cutPos j q` (decidable: `cutPos` is a `Nat`).
§3 THE FAMILY.  `allocPre row q i S p` = `RowShXP 0 row (allocSeg q i S p)` ∧ `row.length ≤
   t2Len q` ∧ the stage-1 value conditions restricted to PRESENT positions (`lkBranch` at
   `t2KHd q` guarded; `AxSpinT2f.spinValsP`; the body's read identities `AxSpinT2f.bodyIds`;
   `AxSpinT2f.spinRmwP`; `t2CpuVals`, `t2RelVals` unchanged — already vacuous at absent positions)
   ∧ `∀ j, cutPos j q < row.length → t2GateOk j row q i` (a row that CONTINUES past a gate took
   the normal arm).  NOT in `allocPre`: stage 1's `lkBranch row (t2KRh q) true` (it is the `rlS`
   gate).  `t2CutAt row q i := ∃ j, row.length = cutPos j q ∧ ¬ t2GateOk j row q i`;
   `t2Cut GD i S p := ∃ q, allocPre (grow GD i) q i S p ∧ t2CutAt (grow GD i) q i`;
   `entersPanic` = the same with `j ≠ ppI` (`AxSpinT2f.panicCut`).
§4 BRIDGES.  `preOfFull` (`allocFull` + the five gates ⇒ `allocPre`); `AxSpinT2f.gatesOfPins`
   (stage 1's `AllocPins` + `allocFull` ⇒ the gates, via `AxSpinT2f.gvGrow`: `graphValue GD
   (i, k)` is the row value); `preOfFullPins`; `fullOfPre` (`allocPre` at length `t2Len q` ⇒
   `allocFull`; the `rlS` gate gives back `lkBranch (t2KRh q) true`); `AxSpinT2f.completeIff`;
   `cutDet` (DETERMINACY: if the row is a cut row for SOME parameters in the family it is one for
   EVERY parameters in the family — `b` from the item at 15, `hb` from `lkBranch`, `n` from the
   spin values, `c` from the item at `t2KPp q + 8`); `notCutAtOfLen`, `notCutOfLen` (pure `¬ t2Cut`
   at a non-designated or gate-passing row end), `notCutOfGates`; `cutNotFull` (a complete row
   is no cut row); `AxSpinT2f.notCutOfComplete`.
§5 GUARDED PINS.  `AllocPins2 GD i q` = stage 1's `AllocPins` MINUS `hdArm`, `rhArm`, `rhCpu`,
   `ppGe`, `ppInt` (derived on the normal arm / refuted on the cut arm by D4 readback in
   AxSpinT2h), every `graphValue … = some …` / `= graphData …` pin GUARDED by its position
   `k < (grow GD i).length` (an absent position has `graphValue = none`; unguarded the family
   would be empty below the pinned positions); the `∀ v, graphValue … = some v → …` pins
   (`poArm`, `npNowrap`, `npNcoll`, `ppArm`) are vacuous at absent positions and kept verbatim.
   `pins2OfPins : AllocPins GD i q → AllocPins2 GD i q`.
§6 IMAGE.  `noffImgOk img i v`: `cpus[cpuOf i].noff`'s image bytes (`cpuZ i + 120 .. +123`) hold
   the 32-bit word `v`, with `0 ≤ v < 2^31 − 1` (pop_off's `noff < 1` test reads `v + 1`, so this
   is exactly what keeps `bge` from firing; xv6-true: `noff ∈ {0,1,2}` at allocproc).  Premise
   form `HimgNoff img A B := ∀ i ∈ [A, B], ∃ v, noffImgOk img i v` (design's `Himgnoff`).

## Deviations from the design (and why)

1. `gateOk` is named `t2GateOk` (`gateOk` exists, AxDefer2) and takes the hart `i` (the cpu of
   the `aq`/`rlL` gates).  Gates are ROW-level (`AxSpinT2f.rv row k = (row[k]?).bind lblValue`),
   the pins' `graphValue` is bridged by `AxSpinT2f.gvGrow`.
2. `t2Cut` QUANTIFIES THE PARAMETERS INSIDE THE FAMILY (`∃ q, allocPre … q … ∧ …`), the design's
   `∃ q j, length = cutPos j q ∧ ¬ gateOk` leaves `q` unconstrained — then a FULL row is a "cut"
   row for a `q'` with more spins (`t2KRh q' + 1 = t2Len q`, the `rlS` gate read landing on the
   terminal store, `lblValue = none`… or on any read with the wrong value), and `¬ t2Cut` would be
   unprovable.  With `q` in the family, `cutDet` makes `¬ t2Cut` follow from the q-indexed
   `¬ t2CutAt row qA` the WPd proves (T2b2: `notCutOfGates`).
3. `preOfFull` needs the five gates as a premise (`allocFull` does not contain `hdArm`/`rhArm`/
   `ppGe`/`ppInt` — they were `AllocPins` fields); `preOfFullPins` takes them from stage 1's pins.
4. The body's `RowSh` conjunct of `RowAllocpidBody` is not restated (it is the prefix shape);
   `allocPre` keeps only its read identities (`AxSpinT2f.bodyIds`); `fullOfPre` rebuilds it.
5. `Himgnoff` is stated existentially (`∃ v, noffImgOk …`) rather than through a decoding function
   `noffImg`; same content (the 4 image bytes are the little-endian bytes of `v`, as `Himgn`).
6. The windowed P-form hook (orchestrator, 2026-10-08) is NOT stated here; this file only gives the
   position vocabulary it needs (`cutPos`, `AxSpinT2f.kEqs`, `cutPosInj`/`cutPosOrd`).

HONESTY.  Definitions and row arithmetic; nothing about values is proved here.  The prefix-closure
caveat (a real panicking hart continues into `panic()` → MMIO, outside the graph tier; the family
cuts BEFORE the off arm's first event) is informal (design §B, Q-S2-6).  A row with a flipped gate
that CONTINUES past the cut is outside the family by the gate conjunct of `allocPre`.

**Reused:** `RowShP`/`rowShP*` (AxSpinRowP), `allocSeg`/`allocSegLen`/`allocFull`/`t2Complete`/
`AllocPins`/`t2CpuVals`/`t2RelVals`/`t2K*`/`AxSpinT2a.segParts`/`AxSpinT2a.kHdEq`/`AxSpinT2a.zLk`/
`AxSpinT2a.zNp`/`cpuZ` (AxSpinT2a), `RowShX`/`xshape`/`rowShX*`/`relSh`/`holdShB`/`holdLen`/
`ppLen`/`relK*` (AxSpinRl1), `lkBranch` (AxSpinHd8), `spinVals`/`aqK*` (AxSpinAqr), `aqFail`
(AxSpinAq), `AxSpinAq1.spinRmw`, `RowAllocpidBody`/`apBodySh` (AxSpinAp7), `poSh` (AxSpinPO4),
`ppSh` (AxSpinPO6), `lblValue`/`graphValue` (AxWp).  New short names (`RowShXP`, `rowShXP*`,
`rowShXOfXP`, `T2Cj`, `cutPos`, `t2GateOk`, `allocPre`, `t2CutAt`, `t2Cut`, `entersPanic`,
`preOfFull`, `preOfFullPins`, `fullOfPre`, `cutDet`, `notCutAtOfLen`, `notCutOfLen`,
`notCutOfGates`, `cutNotFull`, `AllocPins2`, `pins2OfPins`, `noffImgOk`, `HimgNoff`) grepped
absent from the tree; Lean-only helpers are `AxSpinT2f.*`.
-/
import Weak.AxSpinT2a
import Weak.AxSpinRowP

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Prefix shapes over `Rxitem` -/

/-- PREFIX `RowShX`: every item whose row position is present in the row is matched there. -/
def RowShXP (k : Nat) (row : List Lbl) (sh : List Rxitem) : Prop :=
  ∀ j x, sh[j]? = some x → k + j < row.length → ∃ lb, row[k + j]? = some lb ∧ xshape x lb

section shp
variable {k k' : Nat} {row : List Lbl}

theorem rowShXPOfX {sh : List Rxitem} : RowShX k row sh → RowShXP k row sh :=
  fun H j x Hj _ => H j x Hj

theorem rowShXOfXP {sh : List Rxitem} :
    RowShXP k row sh → k + sh.length ≤ row.length → RowShX k row sh := by
  intro H Hl j x Hj
  have : j < sh.length := (List.getElem?_eq_some_iff.1 Hj).1
  exact H j x Hj (by omega)

theorem rowShXPAppL {s1 s2 : List Rxitem} : RowShXP k row (s1 ++ s2) → RowShXP k row s1 :=
  fun H j x Hj Hk => H j x (lookup_app_l_Some Hj) Hk

theorem rowShXPAppR {s1 s2 : List Rxitem} :
    RowShXP k row (s1 ++ s2) → RowShXP (k + s1.length) row s2 := by
  intro H j x Hj Hk
  obtain ⟨lb, Hlb, Hs⟩ := H (s1.length + j) x (by
    rw [List.getElem?_append_right (by omega), show s1.length + j - s1.length = j by omega]
    exact Hj) (by omega)
  exact ⟨lb, by rw [show k + s1.length + j = k + (s1.length + j) by omega]; exact Hlb, Hs⟩

theorem rowShXPMap (sh : List Ritem) : RowShXP k row (sh.map .it) ↔ RowShP k row sh := by
  constructor
  · intro H j it Hj Hk
    exact H j (.it it) (by rw [List.getElem?_map, Hj]; rfl) Hk
  · intro H j x Hj Hk
    rw [List.getElem?_map] at Hj
    cases h : sh[j]? with
    | none => rw [h] at Hj; cases Hj
    | some it =>
      rw [h] at Hj; cases Hj
      exact H j it h Hk

theorem rowShXPCongr {sh : List Rxitem} : RowShXP k row sh → k = k' → RowShXP k' row sh :=
  fun H e => e ▸ H

end shp

/-! ## Segment positions -/

/-- Every segment position in terms of `t2KHd`, `holdLen`, `n`, `ppLen` (for `omega`). -/
theorem AxSpinT2f.kEqs (q : T2Prm) :
    t2KHd q = 20 + (if q.b then 5 else 0) ∧ t2KSp q = t2KHd q + holdLen q.hb ∧
    t2KRl q = t2KSp q + q.n + 76 ∧ t2KRh q = t2KRl q + 3 ∧ t2KPp q = t2KRl q + 18 ∧
    t2Len q = t2KRl q + 22 + ppLen q.c ∧ 1 ≤ holdLen q.hb ∧ holdLen q.hb ≤ 12 ∧
    10 ≤ ppLen q.c := by
  refine ⟨AxSpinT2a.kHdEq q, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [t2KSp, t2KHd, aqKh, holdLen]
  · simp only [t2KRl, t2KBd, t2KMy, t2KSp, aqKm]; omega
  · simp only [t2Len, t2KT, relKe, relKr, relKp]; omega
  · unfold holdLen; split <;> omega
  · unfold holdLen; split <;> omega
  · unfold ppLen; split <;> omega

/-- The segment's pieces at their positions, on a PREFIX (`AxSpinT2a.segParts` on `RowShXP`). -/
theorem AxSpinT2f.segPartsP {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (H : RowShXP 0 row (allocSeg q i S p)) :
    RowShP 0 row (aqHead (S - 8) (S - 16) (S - 24)) ∧
    RowShP t2KPo row (poSh q.b (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
      (cpuZ i + 124)) ∧
    RowShP (t2KHd q) row (holdShB q.hb AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48)
      (S - 56) (S - 72) (S - 80)) ∧
    RowShXP (t2KSp q) row (List.replicate (q.n + 1) (Rxitem.RM true false AxSpinT2a.zLk 4)) ∧
    RowShP (t2KMy q) row (aqTail (S - 40) (S - 48) (AxSpinT2a.zLk + 16) (S - 8) (S - 16) (S - 24)) ∧
    RowShP (t2KBd q) row (apBodySh AxSpinT2a.zNp (p + 48)) ∧
    RowShXP (t2KRl q) row (relSh q.c (S - 8) (S - 16) (S - 24) AxSpinT2a.zLk (AxSpinT2a.zLk + 16)
      (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (S - 40) (S - 48) (S - 56) (S - 64)
      (cpuZ i + 120) (cpuZ i + 124)) ∧
    RowShXP (t2KT q) row [Rxitem.it (.RS (p + 24) 4)] := by
  unfold allocSeg at H
  have R1 := rowShXPAppR H
  have R2 := rowShXPAppR R1
  have R3 := rowShXPAppR R2
  have R4 := rowShXPAppR R3
  have R5 := rowShXPAppR R4
  have R6 := rowShXPAppR R5
  have R7 := rowShXPAppR R6
  simp only [List.length_map, AxSpinT2a.aqHeadLen, AxSpinT2a.poShLen, holdShBLen,
    List.length_replicate, aqTailLen, AxSpinAp7.apBodyShLen, relShLen] at R1 R2 R3 R4 R5 R6 R7
  refine ⟨(rowShXPMap _).1 (rowShXPAppL H), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (rowShXPMap _).1 (rowShXPAppL R1)
  · refine (rowShXPMap _).1 (rowShXPCongr (rowShXPAppL R2) ?_)
    simp only [t2KHd, aqKp]; omega
  · refine rowShXPCongr (rowShXPAppL R3) ?_
    simp only [t2KSp, aqKh, aqKp, holdLen]; omega
  · refine (rowShXPMap _).1 (rowShXPCongr (rowShXPAppL R4) ?_)
    simp only [t2KMy, aqKm, aqKh, aqKp, holdLen]; omega
  · refine (rowShXPMap _).1 (rowShXPCongr (rowShXPAppL R5) ?_)
    simp only [t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; omega
  · refine rowShXPCongr (rowShXPAppL R6) ?_
    simp only [t2KRl, t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; omega
  · refine rowShXPCongr R7 ?_
    simp only [t2KT, relKe, relKr, relKp, relLen, t2KRl, t2KBd, t2KMy, aqKm, aqKh, aqKp,
      holdLen]
    omega

/-! # 2. The designated cuts -/

/-- The five designated cuts (Rocq ID-8 list): acquire's holding long arm, release's holding
short and long arms, pop_off's `noff < 1` (the three/four PANIC arms) and pop_off's `intr_on`. -/
inductive T2Cj where
  | aq
  | rlS
  | rlL
  | ppN
  | ppI
  deriving DecidableEq

/-- The row length at which cut `j`'s off arm would emit its first event. -/
def cutPos : T2Cj → T2Prm → Nat
  | .aq, q => t2KHd q + 12
  | .rlS, q => t2KRh q + 1
  | .rlL, q => t2KRh q + 12
  | .ppN, q => t2KPp q + 7
  | .ppI, q => t2KPp q + 9

/-- (Lean-only) the value a row item reads. -/
def AxSpinT2f.rv (row : List Lbl) (k : Nat) : Option (List (BitVec 8)) := (row[k]?).bind lblValue

/-- Cut `j`'s gate read took the NORMAL arm (vacuous when the read is absent). -/
def t2GateOk : T2Cj → List Lbl → T2Prm → Agent → Prop
  | .aq, row, q, i => q.hb = true → ∀ vs, AxSpinT2f.rv row (t2KHd q + 4) = some vs →
      ldRes false 8 vs ≠ cpuAddr (cpuOf i)
  | .rlS, row, q, _ => ∀ vs, AxSpinT2f.rv row (t2KRh q) = some vs → ldRes false 4 vs ≠ 0#64
  | .rlL, row, q, i => ∀ vs, AxSpinT2f.rv row (t2KRh q + 4) = some vs →
      ldRes false 8 vs = cpuAddr (cpuOf i)
  | .ppN, row, q, _ => ∀ vs, AxSpinT2f.rv row (t2KPp q + 6) = some vs →
      zopz0zKzJ_s zero_reg (ldRes false 4 vs) = false
  | .ppI, row, q, _ => q.c = false → ∀ vs, AxSpinT2f.rv row (t2KPp q + 8) = some vs →
      (ldRes false 4 vs == zero_reg) = true

theorem AxSpinT2f.cutPosLen (j : T2Cj) (q : T2Prm) : cutPos j q < t2Len q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  cases j <;> simp only [cutPos] <;> omega

/-- The cut positions are strictly increasing `aq < rlS < rlL < ppN < ppI`. -/
theorem AxSpinT2f.cutPosOrd (q : T2Prm) :
    cutPos .aq q < cutPos .rlS q ∧ cutPos .rlS q < cutPos .rlL q ∧
    cutPos .rlL q < cutPos .ppN q ∧ cutPos .ppN q < cutPos .ppI q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  simp only [cutPos]; omega

theorem AxSpinT2f.cutPosInj {j j' : T2Cj} {q : T2Prm} : cutPos j q = cutPos j' q → j = j' := by
  intro h
  have O := AxSpinT2f.cutPosOrd q
  cases j <;> cases j' <;> first | rfl | (exfalso; omega)

/-- Every cut lies past acquire's holding window start and past push_off (`> 15`). -/
theorem AxSpinT2f.cutPosGe (j : T2Cj) (q : T2Prm) : t2KHd q + 12 ≤ cutPos j q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  cases j <;> simp only [cutPos] <;> omega

/-- The spins end before every cut but acquire's. -/
theorem AxSpinT2f.spPos (j : T2Cj) (q : T2Prm) (hj : j ≠ .aq) : t2KSp q + q.n < cutPos j q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  cases j <;> simp only [cutPos] <;> first | omega | exact absurd rfl hj

/-! # 3. The family, the cuts -/

/-- `spinVals` on present positions. -/
def AxSpinT2f.spinValsP (row : List Lbl) (u n : Nat) : Prop :=
  ∀ j, j ≤ n → u + j < row.length → ∃ lb vs, row[u + j]? = some lb ∧ lblValue lb = some vs ∧
    aqFail vs = decide (j < n)

/-- `AxSpinAq1.spinRmw` on present positions. -/
def AxSpinT2f.spinRmwP (row : List Lbl) (u n : Nat) (lk : Int) : Prop :=
  ∀ j, j ≤ n → u + j < row.length → ∃ (t : Nat) (rvs : List (BitVec 8)),
    row[u + j]? = some (.LRmw true false lk [t, t, t, t] rvs AxSpinX4.o4 .WCexcl) ∧
    (rvs = AxSpinX4.z4 ∨ ∃ b0', rvs[0]? = some b0' ∧ b0' ≠ b0)

/-- The read identities of `RowAllocpidBody` (already vacuous at absent positions). -/
def AxSpinT2f.bodyIds (k : Nat) (row : List Lbl) (pnp : Int) : Prop :=
  (∀ lb, row[k]? = some lb → aident lb = .IRead false pnp 4) ∧
  (∀ j, j < 64 → ∀ lb, row[k + 1 + j]? = some lb →
    aident lb = .IRead false (AxSpinAp7.scanAddr j) 4)

/-- THE PREFIX FAMILY (one hart): the row is a prefix of the segment's shape, the stage-1 value
conditions hold at the present positions, and a row that continues past a gate took the normal
arm.  (Release's `lkBranch (t2KRh q) true` is NOT here: it is the `rlS` gate.) -/
def allocPre (row : List Lbl) (q : T2Prm) (i : Agent) (S p : Int) : Prop :=
  RowShXP 0 row (allocSeg q i S p) ∧ row.length ≤ t2Len q ∧
  (t2KHd q < row.length → lkBranch row (t2KHd q) q.hb) ∧
  AxSpinT2f.spinValsP row (t2KSp q) q.n ∧
  AxSpinT2f.bodyIds (t2KBd q) row AxSpinT2a.zNp ∧
  AxSpinT2f.spinRmwP row (t2KSp q) q.n AxSpinT2a.zLk ∧ t2CpuVals row i ∧ t2RelVals row q ∧
  (∀ j, cutPos j q < row.length → t2GateOk j row q i)

/-- The row (with parameters `q`) ENDS at a designated cut whose gate took the off arm. -/
def t2CutAt (row : List Lbl) (q : T2Prm) (i : Agent) : Prop :=
  ∃ j, row.length = cutPos j q ∧ ¬ t2GateOk j row q i

/-- Hart `i`'s row is a family row that ends at a taken off arm (panic or `intr_on`). -/
def t2Cut (GD : Gdexec) (i : Agent) (S p : Int) : Prop :=
  ∃ q, allocPre (AxOpsem.grow GD i) q i S p ∧ t2CutAt (AxOpsem.grow GD i) q i

/-- `t2Cut` restricted to the four PANIC arms (`aq`, `rlS`, `rlL`, `ppN`). -/
def entersPanic (GD : Gdexec) (i : Agent) (S p : Int) : Prop :=
  ∃ q j, j ≠ .ppI ∧ allocPre (AxOpsem.grow GD i) q i S p ∧
    (AxOpsem.grow GD i).length = cutPos j q ∧ ¬ t2GateOk j (AxOpsem.grow GD i) q i

theorem AxSpinT2f.panicCut {GD : Gdexec} {i : Agent} {S p : Int} :
    entersPanic GD i S p → t2Cut GD i S p := by
  rintro ⟨q, j, -, H, hL, hG⟩
  exact ⟨q, H, j, hL, hG⟩

/-! ## Determinacy of the parameters on a family row -/

/-- (Lean-only) what determinacy uses: the prefix shape, holding's lock bit and the spins. -/
def AxSpinT2f.preCore (row : List Lbl) (q : T2Prm) (i : Agent) (S p : Int) : Prop :=
  RowShXP 0 row (allocSeg q i S p) ∧ (t2KHd q < row.length → lkBranch row (t2KHd q) q.hb) ∧
  AxSpinT2f.spinValsP row (t2KSp q) q.n

theorem AxSpinT2f.coreOfPre {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) : AxSpinT2f.preCore row q i S p :=
  ⟨H.1, H.2.2.1, H.2.2.2.1⟩

theorem AxSpinT2f.spinValsPOf {row : List Lbl} {u n : Nat} (H : spinVals row u n) :
    AxSpinT2f.spinValsP row u n := fun j hj _ => H j hj

theorem AxSpinT2f.coreOfFull {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (HF : allocFull row q i S p) : AxSpinT2f.preCore row q i S p :=
  ⟨rowShXPOfX HF.1, fun _ => HF.2.2.1, AxSpinT2f.spinValsPOf HF.2.2.2.1⟩

theorem AxSpinT2f.rsRl {pa pa' : Int} {n n' : Nat} {lb : Lbl} :
    ishape (.RS pa n) lb → ishape (.RL pa' n') lb → False := by
  rintro ⟨vw, cls, rfl, -⟩ ⟨aq, h⟩
  simp [aident] at h

theorem AxSpinT2f.rlW {pa pa' : Int} {n n' : Nat} {lb : Lbl} :
    ishape (.RL pa n) lb → ishape (.RL pa' n') lb → n = n' := by
  rintro ⟨aq, h⟩ ⟨aq', h'⟩
  rw [h] at h'
  cases h'
  rfl

/-- push_off's arm is fixed by the item at 15 (intena store vs noff load). -/
theorem AxSpinT2f.bDet {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row q i S p) (H' : AxSpinT2f.preCore row q' i S p)
    (hl : 15 < row.length) : q.b = q'.b := by
  have P := (AxSpinT2f.segPartsP H.1).2.1
  have P' := (AxSpinT2f.segPartsP H'.1).2.1
  have T : (poSh true (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
      (cpuZ i + 124))[12]? = some (.RS (cpuZ i + 124) 4) ∧
    (poSh false (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
      (cpuZ i + 124))[12]? = some (.RL (cpuZ i + 120) 4) := ⟨rfl, rfl⟩
  have hp : t2KPo + 12 < row.length := by simp only [t2KPo]; omega
  revert P P'
  cases q.b <;> cases q'.b <;> intro P P'
  · rfl
  · obtain ⟨lb, h1, s1⟩ := rowShPAt P T.2 hp
    obtain ⟨lb', h1', s1'⟩ := rowShPAt P' T.1 hp
    rw [h1] at h1'; cases h1'
    exact (AxSpinT2f.rsRl s1' s1).elim
  · obtain ⟨lb, h1, s1⟩ := rowShPAt P T.1 hp
    obtain ⟨lb', h1', s1'⟩ := rowShPAt P' T.2 hp
    rw [h1] at h1'; cases h1'
    exact (AxSpinT2f.rsRl s1 s1').elim
  · rfl

/-- holding's lock bit on acquire's call is fixed by its `lkBranch`. -/
theorem AxSpinT2f.hbDet {row : List Lbl} {b hb hb' : Bool} {n n' : Nat} {c c' : Bool}
    {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row ⟨b, hb, n, c⟩ i S p) (H' : AxSpinT2f.preCore row ⟨b, hb', n', c'⟩ i S p)
    (hl : t2KHd ⟨b, hb, n, c⟩ < row.length) : hb = hb' := by
  obtain ⟨lb, vs, h1, h2, h3⟩ := H.2.1 hl
  obtain ⟨lb', vs', h1', h2', h3'⟩ := H'.2.1 hl
  have e : row[t2KHd ⟨b, hb, n, c⟩]? = some lb' := h1'
  rw [h1] at e; cases e
  rw [h2] at h2'; cases h2'
  exact h3.trans h3'.symm

/-- the number of failed spins is fixed by the spin values. -/
theorem AxSpinT2f.nDet {row : List Lbl} {b hb : Bool} {n n' : Nat} {c c' : Bool}
    {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row ⟨b, hb, n, c⟩ i S p) (H' : AxSpinT2f.preCore row ⟨b, hb, n', c'⟩ i S p)
    (hl : t2KSp ⟨b, hb, n', c'⟩ + n' < row.length) : n = n' := by
  have V := H.2.2
  have V' := H'.2.2
  have key : ∀ m, m ≤ n → m ≤ n' → t2KSp ⟨b, hb, n, c⟩ + m < row.length →
      decide (m < n) = decide (m < n') := by
    intro m hm hm' hlm
    obtain ⟨lb, vs, h1, h2, h3⟩ := V m hm hlm
    obtain ⟨lb', vs', h1', h2', h3'⟩ := V' m hm' hlm
    have e : row[t2KSp ⟨b, hb, n, c⟩ + m]? = some lb' := h1'
    rw [h1] at e; cases e
    rw [h2] at h2'; cases h2'
    exact h3.symm.trans h3'
  have hs : t2KSp ⟨b, hb, n, c⟩ = t2KSp ⟨b, hb, n', c'⟩ := rfl
  rcases Nat.lt_trichotomy n n' with h | h | h
  · have := key n (Nat.le_refl _) (Nat.le_of_lt h) (by omega)
    simp only [Nat.lt_irrefl, decide_false, h, decide_true] at this
    exact absurd this (by decide)
  · exact h
  · have := key n' (Nat.le_of_lt h) (Nat.le_refl _) (by omega)
    simp only [Nat.lt_irrefl, decide_false, h, decide_true] at this
    exact absurd this (by decide)

/-- pop_off's arm is fixed by the item at `t2KPp q + 8` (intena load, 4 B, vs ra reload, 8 B). -/
theorem AxSpinT2f.cDet {row : List Lbl} {b hb : Bool} {n : Nat} {c : Bool}
    {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row ⟨b, hb, n, c⟩ i S p)
    (H' : AxSpinT2f.preCore row ⟨b, hb, n, false⟩ i S p)
    (hl : t2KPp ⟨b, hb, n, c⟩ + 8 < row.length) : c = false := by
  cases c
  · rfl
  · exfalso
    have P := (AxSpinT2f.segPartsP H.1).2.2.2.2.2.2.1
    have P' := (AxSpinT2f.segPartsP H'.1).2.2.2.2.2.2.1
    have hp : t2KRl ⟨b, hb, n, true⟩ + 26 < row.length := by
      simp only [t2KPp, relKp] at hl; omega
    obtain ⟨lb, h1, s1⟩ := P 26 _ rfl hp
    obtain ⟨lb', h1', s1'⟩ := P' 26 _ rfl hp
    have e : row[t2KRl ⟨b, hb, n, true⟩ + 26]? = some lb' := h1'
    rw [h1] at e; cases e
    exact absurd (AxSpinT2f.rlW s1 s1') (by decide)

/-- DETERMINACY: a cut row for some family parameters is a cut row for all of them. -/
theorem AxSpinT2f.cutDetCore {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row q i S p) (H' : AxSpinT2f.preCore row q' i S p) :
    t2CutAt row q' i → t2CutAt row q i := by
  rintro ⟨j, hL, hG⟩
  have hge := AxSpinT2f.cutPosGe j q'
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q'
  have hb := AxSpinT2f.bDet H H' (by omega)
  clear k1 k2 k3 k4 k5 k6 k7 k8 k9
  obtain ⟨b, hb0, n, c⟩ := q
  obtain ⟨b', hb', n', c'⟩ := q'
  simp only at hb
  subst hb
  have hhb := AxSpinT2f.hbDet H H' (by show t2KHd ⟨b, hb', n', c'⟩ < row.length; omega)
  subst hhb
  have hn : j ≠ .aq → n = n' := fun hj =>
    AxSpinT2f.nDet H H' (by rw [hL]; exact AxSpinT2f.spPos j _ hj)
  cases j with
  | aq => exact ⟨.aq, hL, hG⟩
  | rlS => obtain rfl := hn (by decide); exact ⟨.rlS, hL, hG⟩
  | rlL => obtain rfl := hn (by decide); exact ⟨.rlL, hL, hG⟩
  | ppN => obtain rfl := hn (by decide); exact ⟨.ppN, hL, hG⟩
  | ppI =>
    obtain rfl := hn (by decide)
    cases c'
    · obtain rfl := AxSpinT2f.cDet H H' (by
        rw [hL]; show t2KPp ⟨b, hb0, n, false⟩ + 8 < t2KPp ⟨b, hb0, n, false⟩ + 9; omega)
      exact ⟨.ppI, hL, hG⟩
    · exfalso
      apply hG
      simp only [t2GateOk]
      intro h
      cases h

/-! # 4. Bridges -/

/-- `graphValue` is the row value. -/
theorem AxSpinT2f.gvGrow (GD : Gdexec) (i k : Nat) :
    graphValue GD (i, k) = AxSpinT2f.rv (AxOpsem.grow GD i) k := by
  unfold graphValue gxLbl AxSpinT2f.rv AxOpsem.grow growG
  rcases GD.gdG.gxProg[i]? with _ | p <;> simp

/-- A FULL row with the five gates passed is in the prefix family. -/
theorem preOfFull {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (HF : allocFull row q i S p) (HG : ∀ j, t2GateOk j row q i) : allocPre row q i S p := by
  obtain ⟨H1, H2, H3, H4, -, H6, H7, H8, H9⟩ := HF
  exact ⟨rowShXPOfX H1, by omega, fun _ => H3, AxSpinT2f.spinValsPOf H4, ⟨H6.2.1, H6.2.2⟩,
    fun j hj _ => H7 j hj, H8, H9, fun j _ => HG j⟩

/-- Stage 1's pins (and `allocFull`'s release lock bit) give the five gates. -/
theorem AxSpinT2f.gatesOfPins {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (HF : allocFull (AxOpsem.grow GD i) q i S p) (HP : AllocPins GD i q) :
    ∀ j, t2GateOk j (AxOpsem.grow GD i) q i := by
  intro j
  cases j with
  | aq =>
    intro hhb vs hv
    exact HP.hdArm hhb vs ((AxSpinT2f.gvGrow GD i _).trans hv)
  | rlS =>
    intro vs hv h0
    obtain ⟨lb, vs', h1, h2, h3⟩ := HF.2.2.2.2.1
    simp only [AxSpinT2f.rv, h1, Option.bind_some, h2, Option.some.injEq] at hv
    subst hv
    rw [h0] at h3
    simp at h3
  | rlL =>
    intro vs hv
    exact HP.rhArm vs ((AxSpinT2f.gvGrow GD i _).trans hv)
  | ppN =>
    intro vs hv
    exact HP.ppGe vs ((AxSpinT2f.gvGrow GD i _).trans hv)
  | ppI =>
    intro hc vs hv
    exact HP.ppInt hc vs ((AxSpinT2f.gvGrow GD i _).trans hv)

/-- Stage 1's family + pins ⇒ the prefix family. -/
theorem preOfFullPins {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (HF : allocFull (AxOpsem.grow GD i) q i S p) (HP : AllocPins GD i q) :
    allocPre (AxOpsem.grow GD i) q i S p :=
  preOfFull HF (AxSpinT2f.gatesOfPins HF HP)

theorem AxSpinT2f.rdVal {lb : Lbl} {aq : Bool} {pa : Int} {n : Nat} :
    aident lb = .IRead aq pa n → ∃ vs, lblValue lb = some vs := by
  cases lb <;> simp [aident, lblValue]

/-- A family row of FULL length is a stage-1 family row. -/
theorem fullOfPre {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) (hl : row.length = t2Len q) : allocFull row q i S p := by
  obtain ⟨H1, -, H3, H4, H5, H6, H7, H8, H9⟩ := H
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  have R : RowShX 0 row (allocSeg q i S p) := rowShXOfXP H1 (by rw [allocSegLen]; omega)
  refine ⟨R, hl, H3 (by omega), fun j hj => H4 j hj (by omega), ?_,
    ⟨(AxSpinT2a.segParts R).2.2.2.2.2.1, H5.1, H5.2⟩, fun j hj => H6 j hj (by omega), H7, H8⟩
  -- release's lock bit: the `rlS` gate at the lock-word read
  have P := (AxSpinT2f.segPartsP H1).2.2.2.2.2.2.1
  have hit : (relSh q.c (S - 8) (S - 16) (S - 24) AxSpinT2a.zLk (AxSpinT2a.zLk + 16)
      (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (S - 40) (S - 48) (S - 56) (S - 64)
      (cpuZ i + 120) (cpuZ i + 124))[3]? = some (.it (.RL AxSpinT2a.zLk 4)) := by
    cases q.c <;> rfl
  obtain ⟨lb, h1, ⟨aq, h2⟩⟩ := P 3 _ hit (by omega)
  obtain ⟨vs, hv⟩ := AxSpinT2f.rdVal h2
  have G := H9 .rlS (by simp only [cutPos]; omega) vs
    (by simp only [AxSpinT2f.rv, t2KRh, relKh, h1, Option.bind_some, hv])
  refine ⟨lb, vs, h1, hv, ?_⟩
  simp [G]

/-- `t2Complete` through the prefix family. -/
theorem AxSpinT2f.completeIff {GD : Gdexec} {i : Agent} {S p : Int}
    (HG : ∀ q, allocFull (AxOpsem.grow GD i) q i S p → ∀ j, t2GateOk j (AxOpsem.grow GD i) q i) :
    t2Complete GD i S p ↔
      ∃ q, allocPre (AxOpsem.grow GD i) q i S p ∧ (AxOpsem.grow GD i).length = t2Len q := by
  constructor
  · rintro ⟨q, HF⟩
    exact ⟨q, preOfFull HF (HG q HF), HF.2.1⟩
  · rintro ⟨q, H, hl⟩
    exact ⟨q, fullOfPre H hl⟩

/-- DETERMINACY on family rows. -/
theorem cutDet {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) (H' : allocPre row q' i S p) :
    t2CutAt row q' i → t2CutAt row q i :=
  AxSpinT2f.cutDetCore (AxSpinT2f.coreOfPre H) (AxSpinT2f.coreOfPre H')

/-- A row ending at no designated position is not a cut row. -/
theorem notCutAtOfLen {row : List Lbl} {q : T2Prm} {i : Agent}
    (h : ∀ j, row.length ≠ cutPos j q) : ¬ t2CutAt row q i :=
  fun ⟨j, hL, _⟩ => h j hL

/-- A row whose end gate (if any) took the normal arm is not a cut row. -/
theorem notCutAtOfGates {row : List Lbl} {q : T2Prm} {i : Agent}
    (h : ∀ j, row.length = cutPos j q → t2GateOk j row q i) : ¬ t2CutAt row q i :=
  fun ⟨j, hL, hG⟩ => hG (h j hL)

/-- `¬ t2Cut` from the q-indexed fact (what the WPd proves for the premise's `q`). -/
theorem notCutOfGates {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p)
    (h : ∀ j, (AxOpsem.grow GD i).length = cutPos j q → t2GateOk j (AxOpsem.grow GD i) q i) :
    ¬ t2Cut GD i S p := by
  rintro ⟨q', H', Hc⟩
  exact notCutAtOfGates h (cutDet H H' Hc)

/-- Pure `¬ t2Cut` at a non-designated row end. -/
theorem notCutOfLen {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p)
    (h : ∀ j, (AxOpsem.grow GD i).length ≠ cutPos j q) : ¬ t2Cut GD i S p :=
  notCutOfGates H (fun j hL => absurd hL (h j))

/-- A complete (stage-1 family) row is no cut row. -/
theorem cutNotFull {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (HF : allocFull (AxOpsem.grow GD i) q i S p) : ¬ t2Cut GD i S p := by
  rintro ⟨q', H', Hc⟩
  obtain ⟨j, hL, -⟩ :=
    AxSpinT2f.cutDetCore (AxSpinT2f.coreOfFull HF) (AxSpinT2f.coreOfPre H') Hc
  have := AxSpinT2f.cutPosLen j q
  rw [HF.2.1] at hL
  omega

theorem AxSpinT2f.notCutOfComplete {GD : Gdexec} {i : Agent} {S p : Int} :
    t2Complete GD i S p → ¬ t2Cut GD i S p :=
  fun ⟨_, HF⟩ => cutNotFull HF

/-! # 5. The guarded pins -/

/-- Stage 1's `AllocPins` MINUS `hdArm`, `rhArm`, `rhCpu`, `ppGe`, `ppInt`, every positional
value pin GUARDED by its position (vacuous on a row that stops before it). -/
structure AllocPins2 (GD : Gdexec) (i : Agent) (q : T2Prm) : Prop where
  /-- push_off's first mycpu (PO1) -/
  poMy1 : t2KPo + 5 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KPo + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))
  /-- push_off's arm `b` (`noff == 0`) -/
  poArm : ∀ vn, graphValue GD (i, t2KPo + 7) = some vn → (ldRes false 4 vn == zero_reg) = q.b
  /-- push_off's second mycpu (the intena arm, PO2) -/
  poMy2 : q.b = true → t2KPo + 10 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KPo + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))
  /-- push_off's tail mycpu (PO3) -/
  poMy3 : t2KPoT q + 2 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KPoT q + 2) = some (stBytes 8 (AxSpinPO.ppo 0x1c))
  /-- push_off's return -/
  poRet : t2KPoT q + 6 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KPoT q + 6) = some (stBytes 8 (AxSpinHdB.pac 0x10))
  /-- holding's mycpu and holding's return (acquire's call, long path) -/
  hdRets : q.hb = true →
    (t2KHd q + 7 < (AxOpsem.grow GD i).length →
      graphValue GD (i, t2KHd q + 7) = some (stBytes 8 (pch 0x1a))) ∧
    (t2KHd q + 9 < (AxOpsem.grow GD i).length →
      graphValue GD (i, t2KHd q + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16)))
  /-- acquire's mycpu -/
  aqMy : t2KMy q + 2 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KMy q + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28))
  /-- acquire's return -/
  aqRet : t2KMy q + 5 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KMy q + 5) = some (stBytes 8 (pca 0x44))
  /-- Q18b: the nextpid read is not 1000 and does not wrap -/
  npNowrap : ∀ vs, graphValue GD (i, t2KBd q) = some vs →
    (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32
  /-- Q18b: no pid collision in the scan -/
  npNcoll : ∀ vs, graphValue GD (i, t2KBd q) = some vs → ∀ j, j < 64 → ∀ v,
    graphValue GD (i, t2KBd q + 1 + j) = some v → (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs
  /-- holding's mycpu and holding's return (release's call) -/
  rhRets : (t2KRh q + 7 < (AxOpsem.grow GD i).length →
      graphValue GD (i, t2KRh q + 7) = some (stBytes 8 (pch 0x1a))) ∧
    (t2KRh q + 9 < (AxOpsem.grow GD i).length →
      graphValue GD (i, t2KRh q + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10)))
  /-- pop_off's mycpu -/
  ppMy : t2KPp q + 4 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KPp q + 4) = some (stBytes 8 (ppp 0x0c))
  /-- pop_off's arm `c` -/
  ppArm : ∀ vn, graphValue GD (i, t2KPp q + 6) = some vn →
    (addiwm1 (ldRes false 4 vn) != zero_reg) = q.c
  /-- pop_off's return -/
  ppRet : t2KPp q + 8 + (if q.c then 0 else 1) < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KPp q + 8 + (if q.c then 0 else 1)) =
      some (stBytes 8 (AxSpinHdB.prl 0x22))
  /-- release's return -/
  rlRet : t2KRr q < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KRr q) = some (stBytes 8 (pca 0x98))
  /-- push_off's s1 reload (acquire's `lk`) -/
  poS1 : t2KPoT q + 8 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KPoT q + 8) = some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  /-- holding's s1 reload on acquire's call -/
  hdS1 : q.hb = true → t2KHd q + 11 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KHd q + 11) = some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  /-- acquire's s1 reload returns acquire's s1 spill -/
  aqS1 : t2KMy q + 7 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KMy q + 7) = graphData GD (i, 2)
  /-- holding's s1 reload on release's call -/
  rhS1 : t2KRh q + 11 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KRh q + 11) = some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  /-- release's s1 reload returns release's s1 spill -/
  rlS1 : t2KRr q + 2 < (AxOpsem.grow GD i).length →
    graphValue GD (i, t2KRr q + 2) = graphData GD (i, t2KRl q + 2)

/-- Stage 1's pins give the guarded ones. -/
theorem pins2OfPins {GD : Gdexec} {i : Agent} {q : T2Prm} (HP : AllocPins GD i q) :
    AllocPins2 GD i q where
  poMy1 _ := HP.poMy1
  poArm := HP.poArm
  poMy2 h _ := HP.poMy2 h
  poMy3 _ := HP.poMy3
  poRet _ := HP.poRet
  hdRets h := ⟨fun _ => (HP.hdRets h).1, fun _ => (HP.hdRets h).2⟩
  aqMy _ := HP.aqMy
  aqRet _ := HP.aqRet
  npNowrap := HP.npNowrap
  npNcoll := HP.npNcoll
  rhRets := ⟨fun _ => HP.rhRets.1, fun _ => HP.rhRets.2⟩
  ppMy _ := HP.ppMy
  ppArm := HP.ppArm
  ppRet _ := HP.ppRet
  rlRet _ := HP.rlRet
  poS1 _ := HP.poS1
  hdS1 h _ := HP.hdS1 h
  aqS1 _ := HP.aqS1
  rhS1 _ := HP.rhS1
  rlS1 _ := HP.rlS1

/-! # 6. The noff image premise -/

/-- `cpus[cpuOf i].noff`'s image bytes hold the 32-bit word `v`, `0 ≤ v < 2^31 − 1`. -/
def noffImgOk (img : Image) (i : Agent) (v : Int) : Prop :=
  0 ≤ v ∧ v < 2 ^ 31 - 1 ∧
  ∀ (j : Nat) (b : BitVec 8), (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b →
    img (cpuZ i + 120 + j) = some b

/-- The design's `Himgnoff` (scope premise Q-S2-3), for harts A and B. -/
def HimgNoff (img : Image) (A B : Agent) : Prop := ∀ i, i ∈ [A, B] → ∃ v, noffImgOk img i v

end Weak
