/-
Weak: **THEOREM 2, STAGE 2 — THE PREFIX ROW FAMILY** (pure): the cut-off rows `allocPre` of the
inlined allocpid segment, the DESIGNATED CUTS — five panic / `intr_on` cuts (`T2Cj`, `cutPos`,
`t2GateOk`) and 18 RELOAD cuts (`T2Rj`, `rlPos`, `rlGateOk`) — in ONE cut family (`t2CutAt`,
`t2Cut`, read three ways: `entersPanic`, `intrOnCut`, `reloadMis`), the GUARDED pins
`AllocPins2`, the noff image premise form `noffImgOk`, and the bridges from stage 1.  Stage-2
design `notes/weak-lb-thm2-stage2.md` §A (spec) and §C row `AxSpinT2f`; reload cuts: design
`notes/weak-lb-thm2-pins.md` §P1 (owner ruling 2026-10-08: restated IN PLACE, one cut family).
NEW Lean file (no Rocq source; Rocq's ID-8 prefix family is the model).

## What this file provides (the interface for AxSpinT2h, the Ap9/ApA P-forms, ApB, T2b2, T2p*)

§1 PREFIX SHAPES over `Rxitem`.  `RowShXP k row sh` (the `Rxitem` twin of AxSpinRowP's
   `RowShP`): every item whose row position `k + j` is PRESENT is matched (`xshape`); lemmas
   `rowShXPOfX` (`RowShX ⇒ RowShXP`), `rowShXOfXP` (full length ⇒ `RowShX`), `rowShXPAppL/AppR`,
   `rowShXPMap` (`↔ RowShP` of the `Ritem` list), `rowShXPCongr`; `AxSpinT2f.segPartsP` = stage 1's
   `AxSpinT2a.segParts` on prefixes (each piece of `allocSeg` as `RowShP`/`RowShXP` at its
   position).  Every row position is an instruction boundary (Stage C: items are memory events,
   the fence is one item, no fetch / walker items under the warm TLB), so no `bnd` bookkeeping.
§2 THE DESIGNATED CUTS.  (a) PANIC / `intr_on`: `T2Cj` = `aq | rlS | rlL | ppN | ppI`; `cutPos j q`
   (the row length at which the off arm's first event would be the next item) and
   `t2GateOk j row q i` (the gate read took the NORMAL arm; vacuous when the read is absent):
   | j     | gate read (position)                       | normal arm (`t2GateOk`)            | `cutPos`      |
   | `aq`  | acquire's holding `ld lk->cpu` `t2KHd q+4` | `hb → value ≠ cpuAddr (cpuOf i)`    | `t2KHd q+12`  |
   | `rlS` | release's holding `lw lk->locked` `t2KRh q`| value `≠ 0` (long arm)              | `t2KRh q+1`   |
   | `rlL` | release's holding `ld lk->cpu` `t2KRh q+4` | value `= cpuAddr (cpuOf i)`         | `t2KRh q+12`  |
   | `ppN` | pop_off's `lw noff` `t2KPp q+6`            | `bge zero,noff` falls (`noff ≥ 1`)  | `t2KPp q+7`   |
   | `ppI` | pop_off's `lw intena` `t2KPp q+8`          | `c = false → intena = 0`            | `t2KPp q+9`   |
   `aq`, `rlS`, `rlL`, `ppN` are the PANIC arms (`entersPanic`); `ppI` is the `intr_on` arm, an
   off-path exit from the SIE = 0 regime (not a panic; Rocq: "the intr_on arm is a cut too").
   Positions: `AxSpinT2f.cutPosLen` (`cutPos j q < t2Len q`), strictly increasing in `j`
   (`AxSpinT2f.cutPosOrd`), `AxSpinT2f.cutPosInj` (AMONG `T2Cj` only), `AxSpinT2f.cutPosGe`,
   `AxSpinT2f.spPos`; `AxSpinT2f.kEqs` = every segment position in terms of `t2KHd`, `holdLen`,
   `n`, `ppLen`.
   (b) RELOADS: `T2Rj` (the 18 reloads that were stage 1's / `AllocPins2`'s reload pins; `hdRets`
   and `rhRets` count two each), the reload's row position `rlKr x q`, the cut position
   `rlPos x q := rlKr x q + 1` (the row ends right after the reload), the presence guard
   `rlOn x q : Bool` (`poMy2` only on `b`, the three `hd*` only on `hb`) and the expected bytes
   `rlExp x row q`:
   | x     | `rlKr`              | `rlExp`              | x     | `rlKr`                     | `rlExp`              |
   | poMy1 | `t2KPo+5`           | `stBytes 8 (ppo 0x14)` | aqRet | `t2KMy q+5`              | `stBytes 8 (pca 0x44)` |
   | poMy2 | `t2KPo+10` (b)      | `stBytes 8 (ppo 0x30)` | aqS1  | `t2KMy q+7`              | spill data `wd row 2`  |
   | poMy3 | `t2KPoT q+2`        | `stBytes 8 (ppo 0x1c)` | rhMy  | `t2KRh q+7`              | `stBytes 8 (pch 0x1a)` |
   | poRet | `t2KPoT q+6`        | `stBytes 8 (pac 0x10)` | rhRet | `t2KRh q+9`              | `stBytes 8 (prl 0x10)` |
   | poS1  | `t2KPoT q+8`        | `stBytes 8 pid_lock`   | rhS1  | `t2KRh q+11`             | `stBytes 8 pid_lock`   |
   | hdMy  | `t2KHd q+7` (hb)    | `stBytes 8 (pch 0x1a)` | ppMy  | `t2KPp q+4`              | `stBytes 8 (ppp 0x0c)` |
   | hdRet | `t2KHd q+9` (hb)    | `stBytes 8 (pac 0x16)` | ppRet | `t2KPp q+8+(c ? 0 : 1)`  | `stBytes 8 (prl 0x22)` |
   | hdS1  | `t2KHd q+11` (hb)   | `stBytes 8 pid_lock`   | rlRet | `t2KRr q`                | `stBytes 8 (pca 0x98)` |
   | aqMy  | `t2KMy q+2`         | `stBytes 8 (pac 0x28)` | rlS1  | `t2KRr q+2`              | `wd row (t2KRl q+2)`   |
   (`AxSpinT2f.wd row k = (row[k]?).bind lblData`; `AxSpinT2f.wdGrow`: `graphData GD (i, k)` is
   it.)  THE RELOAD GATE `rlGateOk x row q := rlOn x q = true → ∀ vs, rv row (rlKr x q) = some vs
   → rlExp x row q = some vs` ("the reload read its spill").  `AxSpinT2f.rlPosLen`,
   `AxSpinT2f.rlPosGe` (every reload cut but `poMy1` lies past push_off's `noff` read).
   COLLIDING POSITIONS (honest): reload cuts share row ends with panic cuts and with each other —
   `hdS1` (`t2KHd q + 12 = cutPos .aq q`), `rhS1` (`= cutPos .rlL q`), `ppRet` at `c = true`
   (`= cutPos .ppI q`, whose gate is then vacuous), `poMy2` (b) / `poMy3` (¬b) (both 14).  No
   position injectivity across the families: a row end is classified by WHICH GATE FAILED, never
   by its length; at a shared end both gates may fail and both readings are then true.
§3 THE FAMILY.  `allocPre row q i S p` = `RowShXP 0 row (allocSeg q i S p)` ∧ `row.length ≤
   t2Len q` ∧ the stage-1 value conditions restricted to PRESENT positions (`lkBranch` at
   `t2KHd q` guarded; `AxSpinT2f.spinValsP`; the body's read identities `AxSpinT2f.bodyIds`;
   `AxSpinT2f.spinRmwP`; `t2CpuVals`, `t2RelVals` unchanged — already vacuous at absent positions)
   ∧ `∀ j, cutPos j q < LEN → t2GateOk j row q i` ∧ push_off's branch bit `AxSpinT2f.poBranch`
   (`t2KPo + 7 < LEN → ∃ vs, rv row (t2KPo+7) = some vs ∧ (ldRes false 4 vs == zero_reg) = q.b`;
   REQUIRED for determinacy: at LEN = 14 the prefix shapes of `b = true` / `b = false` coincide,
   but the reload at 13 must read `ppo 0x30` resp. `ppo 0x1c`) ∧ `∀ x, rlPos x q < LEN →
   rlGateOk x row q` (a row that CONTINUES past a gate — panic or reload — took the normal arm).
   Accessors `AxSpinT2f.gatesOf`/`brOf`/`rlGatesOf`.  NOT in `allocPre`: stage 1's
   `lkBranch row (t2KRh q) true` (it is the `rlS` gate).
   THE CUTS: `rlCutAt row q := ∃ x, LEN = rlPos x q ∧ ¬ rlGateOk x row q`;
   `t2CutAt row q i := (∃ j, LEN = cutPos j q ∧ ¬ t2GateOk j row q i) ∨ rlCutAt row q`;
   `t2Cut GD i S p := ∃ q, allocPre (grow GD i) q i S p ∧ t2CutAt (grow GD i) q i`.  Its three
   readings, stated separately: `entersPanic` (a panic gate `j ≠ ppI` failed), `intrOnCut` (the
   `ppI` gate failed), `reloadMis` (a reload gate failed: "a reload read a wrong value");
   `cutIff : t2Cut ↔ entersPanic ∨ intrOnCut ∨ reloadMis`; `AxSpinT2f.panicCut`/`reloadCut`.
§4 BRIDGES AND DETERMINACY.  `preOfFull` (`allocFull` + the five gates + `poBranch` + the reload
   gates ⇒ `allocPre`); `AxSpinT2f.gatesOfPins`/`brOfArm`/`rlGatesOfPins` (stage 1's `AllocPins`
   (+ `allocFull`) ⇒ them, via `AxSpinT2f.gvGrow`/`wdGrow`); `preOfFullPins`; `fullOfPre`
   (`allocPre` at length `t2Len q` ⇒ `allocFull`); `AxSpinT2f.completeIff`; `AxSpinT2f.qEqFull`
   (a complete row fixes `q`); `cutDet` (DETERMINACY: a cut row for SOME family parameters is
   one for EVERY family parameters — panic part `AxSpinT2f.cutDetCore`: `b` from the item at 15,
   `hb` from `lkBranch`, `n` from the spin values, `c` from the item at `t2KPp q + 8`; reload
   part `AxSpinT2f.rlDet`: `b` from `poBranch`, `hb`/`n`/`c` where the reload position depends on
   them); `notCutAtOfLen`, `notCutAtOfGates`, `notCutOfLen`, `notCutOfGates` (each with a
   panic and a reload premise); `cutNotFull`; `AxSpinT2f.notCutOfComplete`.  Reads:
   `AxSpinT2f.rlRd` (a present on-path reload carries a value), `AxSpinT2f.poArmOf` (stage 1's
   `poArm` from `allocPre`).
§5 GUARDED PINS.  `AllocPins2 GD i q` = stage 1's `AllocPins` MINUS the arm pins `hdArm`, `rhArm`,
   `rhCpu`, `ppGe`, `ppInt` (derived on the normal arm / refuted at the cut by D4 readback in
   AxSpinT2h), MINUS the 18 RELOAD pins (now `allocPre`'s reload gates) and MINUS the selector
   `poArm` (now `allocPre`'s `poBranch`, `AxSpinT2f.poArmOf`).  Kept: `npNowrap`, `npNcoll`
   (Q18b), `ppArm` (selects `q.c`), and the INTERIM premise
   `rlEnd : ∀ x, LEN = rlPos x q → rlGateOk x (grow GD i) q` — a row that ENDS right after a
   reload read the spill there.  `rlEnd` exists because the leaf P-forms (E8, PO4, HdA/Hd9, Aq2,
   PO6, Rl4b) still take the GUARDED pins `kr < LEN → graphValue (i, kr) = vw`, which `allocPre`'s
   gate gives only for `kr + 1 < LEN`; THE BRIDGE `AxSpinT2f.pinOf` (`allocPre` + `rlEnd` ⇒ the
   old guarded pin; `AxSpinT2f.pinOfD` for the two `graphData` forms) supplies them.  When the
   leaf lanes take `AxSpinT2i.Gate` (whose body is `AxSpinT2f.gateBody`, from `allocPre` ALONE),
   the row end `kr + 1` is REFUTED by `cutReload` and `rlEnd` is deleted.  `pins2OfPins :
   AllocPins GD i q → AllocPins2 GD i q`; `AxSpinT2f.notRlCutOf` (`rlEnd` ⇒ `¬ rlCutAt`).
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
3. `preOfFull` needs the gates as premises (`allocFull` does not contain `hdArm`/`rhArm`/`ppGe`/
   `ppInt`/`poArm`/the reload values — they were `AllocPins` fields); `preOfFullPins` takes them
   from stage 1's pins.
4. The body's `RowSh` conjunct of `RowAllocpidBody` is not restated (it is the prefix shape);
   `allocPre` keeps only its read identities (`AxSpinT2f.bodyIds`); `fullOfPre` rebuilds it.
5. `Himgnoff` is stated existentially (`∃ v, noffImgOk …`) rather than through a decoding function
   `noffImg`; same content (the 4 image bytes are the little-endian bytes of `v`, as `Himgn`).
6. The windowed P-form hook (orchestrator, 2026-10-08) is NOT stated here; this file only gives the
   position vocabulary it needs (`cutPos`, `rlPos`, `AxSpinT2f.kEqs`, `cutPosInj`/`cutPosOrd`).
7. (P1, owner ruling 2026-10-08) The reload cuts are a SECOND index type `T2Rj` beside `T2Cj`
   (not 18 more `T2Cj` constructors): `cutPosInj`/`cutPosGe`/`spPos` stay TRUE as stated for the
   panic / `intr_on` cuts, and nothing is claimed about positions across the families (they
   collide, §2).  The one cut family is `t2CutAt`/`t2Cut` (disjunction over both).
   `intr_on`'s reading is `intrOnCut` (`intrOn` is AxIntr's SIE predicate).  `rlExp` is an
   `Option` so the two spill-data reloads share the definition (`some e = some vs` for a literal).
8. (P1) `poArm` is DROPPED from `AllocPins2` (redundant with `allocPre`'s `poBranch`,
   `AxSpinT2f.poArmOf`); `ppArm` is kept (`c` is not determined by `allocPre`'s value conditions).
9. (P1, INTERIM, see §5) `AllocPins2.rlEnd`: until the leaf lanes switch to gates, a row that ends
   exactly at `rlPos x q` with a wrong reload is EXCLUDED by this premise rather than refuted, so
   `¬ t2Cut`'s reload reading (`¬ reloadMis`) is, for now, a consequence of `rlEnd` (plus the
   gates of `allocPre` for rows that continue).  The 18 positional pins are gone.

HONESTY.  Definitions and row arithmetic; nothing about values is proved here.  The prefix-closure
caveat (a real panicking hart continues into `panic()` → MMIO, outside the graph tier; the family
cuts BEFORE the off arm's first event) is informal (design §B, Q-S2-6).  A row with a flipped gate
(panic or reload) that CONTINUES past the cut is outside the family by the gate conjuncts of
`allocPre`; for the reloads this needs no MMIO argument (truncating right after the reload).

**Reused:** `RowShP`/`rowShP*` (AxSpinRowP), `allocSeg`/`allocSegLen`/`allocFull`/`t2Complete`/
`AllocPins`/`t2CpuVals`/`t2RelVals`/`t2K*`/`AxSpinT2a.segParts`/`AxSpinT2a.kHdEq`/`AxSpinT2a.zLk`/
`AxSpinT2a.zNp`/`cpuZ` (AxSpinT2a), `RowShX`/`xshape`/`rowShX*`/`relSh`/`holdShB`/`holdLen`/
`ppLen`/`relK*` (AxSpinRl1), `lkBranch` (AxSpinHd8), `spinVals`/`aqK*` (AxSpinAqr), `aqFail`
(AxSpinAq), `AxSpinAq1.spinRmw`, `RowAllocpidBody`/`apBodySh` (AxSpinAp7), `poSh` (AxSpinPO4),
`ppSh` (AxSpinPO6), `lblValue`/`graphValue`/`graphData` (AxWp), `lblData` (AxOpsem); proofs of
the reload cuts from the (deleted) additive draft AxSpinT2f3.  New short names (`RowShXP`,
`rowShXP*`, `rowShXOfXP`, `T2Cj`, `cutPos`, `t2GateOk`, `T2Rj`, `rlKr`, `rlPos`, `rlOn`, `rlExp`,
`rlGateOk`, `allocPre`, `rlCutAt`, `t2CutAt`, `t2Cut`, `entersPanic`, `intrOnCut`, `reloadMis`,
`cutIff`, `preOfFull`, `preOfFullPins`, `fullOfPre`, `cutDet`, `notCutAtOfLen`, `notCutAtOfGates`,
`notCutOfLen`, `notCutOfGates`, `cutNotFull`, `AllocPins2`, `pins2OfPins`, `noffImgOk`,
`HimgNoff`) grepped absent from the tree; Lean-only helpers are `AxSpinT2f.*`.
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

/-- The five designated PANIC / `intr_on` cuts (Rocq ID-8 list): acquire's holding long arm,
release's holding short and long arms, pop_off's `noff < 1` (the four PANIC arms) and pop_off's
`intr_on`.  The 18 RELOAD cuts are `T2Rj` below. -/
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

/-- (Lean-only) the data a row item writes. -/
def AxSpinT2f.wd (row : List Lbl) (k : Nat) : Option (List (BitVec 8)) := (row[k]?).bind lblData

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

/-- The panic / `intr_on` cut positions are strictly increasing `aq < rlS < rlL < ppN < ppI`. -/
theorem AxSpinT2f.cutPosOrd (q : T2Prm) :
    cutPos .aq q < cutPos .rlS q ∧ cutPos .rlS q < cutPos .rlL q ∧
    cutPos .rlL q < cutPos .ppN q ∧ cutPos .ppN q < cutPos .ppI q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  simp only [cutPos]; omega

/-- Injectivity AMONG THE FIVE panic / `intr_on` cuts (reload cuts share row ends with them and
with each other — no injectivity across the two families is claimed). -/
theorem AxSpinT2f.cutPosInj {j j' : T2Cj} {q : T2Prm} : cutPos j q = cutPos j' q → j = j' := by
  intro h
  have O := AxSpinT2f.cutPosOrd q
  cases j <;> cases j' <;> first | rfl | (exfalso; omega)

/-- Every panic / `intr_on` cut lies past acquire's holding window start (`> 15`). -/
theorem AxSpinT2f.cutPosGe (j : T2Cj) (q : T2Prm) : t2KHd q + 12 ≤ cutPos j q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  cases j <;> simp only [cutPos] <;> omega

/-- The spins end before every panic / `intr_on` cut but acquire's. -/
theorem AxSpinT2f.spPos (j : T2Cj) (q : T2Prm) (hj : j ≠ .aq) : t2KSp q + q.n < cutPos j q := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q
  cases j <;> simp only [cutPos] <;> first | omega | exact absurd rfl hj

/-! ## The reload cuts -/

/-- The 18 reloads of the segment (stage 1's reload pins; `hdRets`/`rhRets` are two each): the
11 return-address and 5 `s1` reloads plus mycpu's own `ra` reloads in holding. -/
inductive T2Rj where
  | poMy1 | poMy2 | poMy3 | poRet | poS1
  | hdMy | hdRet | hdS1
  | aqMy | aqRet | aqS1
  | rhMy | rhRet | rhS1
  | ppMy | ppRet | rlRet | rlS1
  deriving DecidableEq

/-- The reload's row position. -/
def rlKr : T2Rj → T2Prm → Nat
  | .poMy1, _ => t2KPo + 5
  | .poMy2, _ => t2KPo + 10
  | .poMy3, q => t2KPoT q + 2
  | .poRet, q => t2KPoT q + 6
  | .poS1, q => t2KPoT q + 8
  | .hdMy, q => t2KHd q + 7
  | .hdRet, q => t2KHd q + 9
  | .hdS1, q => t2KHd q + 11
  | .aqMy, q => t2KMy q + 2
  | .aqRet, q => t2KMy q + 5
  | .aqS1, q => t2KMy q + 7
  | .rhMy, q => t2KRh q + 7
  | .rhRet, q => t2KRh q + 9
  | .rhS1, q => t2KRh q + 11
  | .ppMy, q => t2KPp q + 4
  | .ppRet, q => t2KPp q + 8 + (if q.c then 0 else 1)
  | .rlRet, q => t2KRr q
  | .rlS1, q => t2KRr q + 2

/-- The reload cut's position: the row ends right after the reload. -/
def rlPos (x : T2Rj) (q : T2Prm) : Nat := rlKr x q + 1

/-- The reload is on the run's path (`poMy2` on push_off's intena arm, `hd*` on holding's long
path). -/
def rlOn : T2Rj → T2Prm → Bool
  | .poMy2, q => q.b
  | .hdMy, q => q.hb
  | .hdRet, q => q.hb
  | .hdS1, q => q.hb
  | _, _ => true

/-- The bytes the reload must read (its spill's): a literal, or for `aqS1`/`rlS1` the spill's own
label data. -/
def rlExp : T2Rj → List Lbl → T2Prm → Option (List (BitVec 8))
  | .poMy1, _, _ => some (stBytes 8 (AxSpinPO.ppo 0x14))
  | .poMy2, _, _ => some (stBytes 8 (AxSpinPO.ppo 0x30))
  | .poMy3, _, _ => some (stBytes 8 (AxSpinPO.ppo 0x1c))
  | .poRet, _, _ => some (stBytes 8 (AxSpinHdB.pac 0x10))
  | .poS1, _, _ => some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  | .hdMy, _, _ => some (stBytes 8 (pch 0x1a))
  | .hdRet, _, _ => some (stBytes 8 (AxSpinHdB.pac 0x16))
  | .hdS1, _, _ => some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  | .aqMy, _, _ => some (stBytes 8 (AxSpinHdB.pac 0x28))
  | .aqRet, _, _ => some (stBytes 8 (pca 0x44))
  | .aqS1, row, _ => AxSpinT2f.wd row 2
  | .rhMy, _, _ => some (stBytes 8 (pch 0x1a))
  | .rhRet, _, _ => some (stBytes 8 (AxSpinHdB.prl 0x10))
  | .rhS1, _, _ => some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  | .ppMy, _, _ => some (stBytes 8 (ppp 0x0c))
  | .ppRet, _, _ => some (stBytes 8 (AxSpinHdB.prl 0x22))
  | .rlRet, _, _ => some (stBytes 8 (pca 0x98))
  | .rlS1, row, q => AxSpinT2f.wd row (t2KRl q + 2)

/-- THE RELOAD GATE: the reload (if on the path and present) read its spill. -/
def rlGateOk (x : T2Rj) (row : List Lbl) (q : T2Prm) : Prop :=
  rlOn x q = true → ∀ vs, AxSpinT2f.rv row (rlKr x q) = some vs → rlExp x row q = some vs

/-- (Lean-only) unfold every segment position, split the `if`s, `omega`. -/
local macro "ax_spin_t2f_pos" : tactic =>
  `(tactic| ((try simp only [rlPos, rlKr, t2Len, t2KT, relKe, t2KPoT, t2KPo, t2KHd, t2KSp,
      t2KMy, t2KBd, t2KRl, t2KRh, t2KPp, t2KRr, aqKp, aqKh, aqKm, relKh, relKp, relKr, ppLen,
      holdLen, Bool.false_eq_true, ↓reduceIte]) <;> (try split) <;> (try split) <;>
      (try split) <;> omega))

theorem AxSpinT2f.rlPosLen (x : T2Rj) (q : T2Prm) : rlPos x q < t2Len q := by
  obtain ⟨b, hb, n, c⟩ := q
  cases x <;> ax_spin_t2f_pos

/-- Every reload cut but `poMy1` lies past push_off's `noff` read. -/
theorem AxSpinT2f.rlPosGe (x : T2Rj) (q : T2Prm) : x = .poMy1 ∨ t2KPo + 7 < rlPos x q := by
  obtain ⟨b, hb, n, c⟩ := q
  cases x <;> first
    | exact Or.inl rfl
    | (right; ax_spin_t2f_pos)

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

/-- push_off's branch bit as a row fact (stage 1's `poArm`, on the row): REQUIRED for
determinacy of the reload cuts (at row length 14 the prefix shapes of `b = true` / `b = false`
coincide, but the reload at 13 must read `ppo 0x30` resp. `ppo 0x1c`). -/
def AxSpinT2f.poBranch (row : List Lbl) (q : T2Prm) : Prop :=
  t2KPo + 7 < row.length → ∃ vs, AxSpinT2f.rv row (t2KPo + 7) = some vs ∧
    (ldRes false 4 vs == zero_reg) = q.b

/-- THE PREFIX FAMILY (one hart): the row is a prefix of the segment's shape, the stage-1 value
conditions hold at the present positions, push_off's branch bit is the row's, and a row that
continues past a gate — panic / `intr_on` or RELOAD — took the normal arm.  (Release's
`lkBranch (t2KRh q) true` is NOT here: it is the `rlS` gate.) -/
def allocPre (row : List Lbl) (q : T2Prm) (i : Agent) (S p : Int) : Prop :=
  RowShXP 0 row (allocSeg q i S p) ∧ row.length ≤ t2Len q ∧
  (t2KHd q < row.length → lkBranch row (t2KHd q) q.hb) ∧
  AxSpinT2f.spinValsP row (t2KSp q) q.n ∧
  AxSpinT2f.bodyIds (t2KBd q) row AxSpinT2a.zNp ∧
  AxSpinT2f.spinRmwP row (t2KSp q) q.n AxSpinT2a.zLk ∧ t2CpuVals row i ∧ t2RelVals row q ∧
  (∀ j, cutPos j q < row.length → t2GateOk j row q i) ∧
  AxSpinT2f.poBranch row q ∧
  (∀ x, rlPos x q < row.length → rlGateOk x row q)

section acc
variable {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}

/-- (Lean-only) `allocPre`'s panic / `intr_on` gate conjunct. -/
theorem AxSpinT2f.gatesOf (H : allocPre row q i S p) :
    ∀ j, cutPos j q < row.length → t2GateOk j row q i := H.2.2.2.2.2.2.2.2.1

/-- (Lean-only) `allocPre`'s push_off branch conjunct. -/
theorem AxSpinT2f.brOf (H : allocPre row q i S p) : AxSpinT2f.poBranch row q :=
  H.2.2.2.2.2.2.2.2.2.1

/-- (Lean-only) `allocPre`'s reload gate conjunct. -/
theorem AxSpinT2f.rlGatesOf (H : allocPre row q i S p) :
    ∀ x, rlPos x q < row.length → rlGateOk x row q := H.2.2.2.2.2.2.2.2.2.2

end acc

/-- The row ends right after a reload (on the path) that read a value other than its spill. -/
def rlCutAt (row : List Lbl) (q : T2Prm) : Prop :=
  ∃ x, row.length = rlPos x q ∧ ¬ rlGateOk x row q

/-- The row (with parameters `q`) ENDS at a designated cut whose gate took the off arm: a panic /
`intr_on` gate `j`, or a reload `x` that misread.  Classified by WHICH GATE FAILED (a row end may
be several cut positions at once). -/
def t2CutAt (row : List Lbl) (q : T2Prm) (i : Agent) : Prop :=
  (∃ j, row.length = cutPos j q ∧ ¬ t2GateOk j row q i) ∨ rlCutAt row q

/-- Hart `i`'s row is a family row that ends at a taken off arm (panic, `intr_on`, or a reload
misread). -/
def t2Cut (GD : Gdexec) (i : Agent) (S p : Int) : Prop :=
  ∃ q, allocPre (AxOpsem.grow GD i) q i S p ∧ t2CutAt (AxOpsem.grow GD i) q i

/-- The row PANICS: one of the four PANIC gates (`aq`, `rlS`, `rlL`, `ppN`) failed at the row end. -/
def entersPanic (GD : Gdexec) (i : Agent) (S p : Int) : Prop :=
  ∃ q j, j ≠ .ppI ∧ allocPre (AxOpsem.grow GD i) q i S p ∧
    (AxOpsem.grow GD i).length = cutPos j q ∧ ¬ t2GateOk j (AxOpsem.grow GD i) q i

/-- The row takes pop_off's `intr_on` arm (the `ppI` gate failed at the row end). -/
def intrOnCut (GD : Gdexec) (i : Agent) (S p : Int) : Prop :=
  ∃ q, allocPre (AxOpsem.grow GD i) q i S p ∧
    (AxOpsem.grow GD i).length = cutPos .ppI q ∧ ¬ t2GateOk .ppI (AxOpsem.grow GD i) q i

/-- A RELOAD READ A WRONG VALUE (the row ends right after it). -/
def reloadMis (GD : Gdexec) (i : Agent) (S p : Int) : Prop :=
  ∃ q, allocPre (AxOpsem.grow GD i) q i S p ∧ rlCutAt (AxOpsem.grow GD i) q

/-- The three readings of a cut row. -/
theorem cutIff {GD : Gdexec} {i : Agent} {S p : Int} :
    t2Cut GD i S p ↔ entersPanic GD i S p ∨ intrOnCut GD i S p ∨ reloadMis GD i S p := by
  constructor
  · rintro ⟨q, H, ⟨j, hL, hG⟩ | hr⟩
    · by_cases hj : j = .ppI
      · subst hj
        exact Or.inr (Or.inl ⟨q, H, hL, hG⟩)
      · exact Or.inl ⟨q, j, hj, H, hL, hG⟩
    · exact Or.inr (Or.inr ⟨q, H, hr⟩)
  · rintro (⟨q, j, -, H, hL, hG⟩ | ⟨q, H, hL, hG⟩ | ⟨q, H, hr⟩)
    · exact ⟨q, H, Or.inl ⟨j, hL, hG⟩⟩
    · exact ⟨q, H, Or.inl ⟨.ppI, hL, hG⟩⟩
    · exact ⟨q, H, Or.inr hr⟩

theorem AxSpinT2f.panicCut {GD : Gdexec} {i : Agent} {S p : Int} :
    entersPanic GD i S p → t2Cut GD i S p :=
  fun h => cutIff.2 (Or.inl h)

theorem AxSpinT2f.reloadCut {GD : Gdexec} {i : Agent} {S p : Int} :
    reloadMis GD i S p → t2Cut GD i S p :=
  fun h => cutIff.2 (Or.inr (Or.inr h))

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

/-- pop_off's arm is fixed past its intena read (both directions of `AxSpinT2f.cDet`). -/
theorem AxSpinT2f.cEq {row : List Lbl} {b hb : Bool} {n : Nat} {c c' : Bool}
    {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row ⟨b, hb, n, c⟩ i S p) (H' : AxSpinT2f.preCore row ⟨b, hb, n, c'⟩ i S p)
    (hl : t2KPp ⟨b, hb, n, c⟩ + 8 < row.length) : c = c' := by
  cases c' with
  | false => exact AxSpinT2f.cDet H H' hl
  | true =>
    cases c with
    | true => rfl
    | false => exact (AxSpinT2f.cDet H' H hl).symm

/-- DETERMINACY of the PANIC / `intr_on` part: a panic / `intr_on` cut row for some family
parameters is one for all of them. -/
theorem AxSpinT2f.cutDetCore {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row q i S p) (H' : AxSpinT2f.preCore row q' i S p) :
    (∃ j, row.length = cutPos j q' ∧ ¬ t2GateOk j row q' i) →
      ∃ j, row.length = cutPos j q ∧ ¬ t2GateOk j row q i := by
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

/-- push_off's arm is fixed by `poBranch`. -/
theorem AxSpinT2f.bDetBr {row : List Lbl} {q q' : T2Prm} (H : AxSpinT2f.poBranch row q)
    (H' : AxSpinT2f.poBranch row q') (hl : t2KPo + 7 < row.length) : q.b = q'.b := by
  obtain ⟨vs, h1, h2⟩ := H hl
  obtain ⟨vs', h1', h2'⟩ := H' hl
  rw [h1] at h1'
  cases h1'
  exact h2.symm.trans h2'

/-- DETERMINACY of the RELOAD part: `b` from `poBranch`, `hb`/`n`/`c` from `hbDet`/`nDet`/`cEq`,
each only where the reload position depends on it. -/
theorem AxSpinT2f.rlDet {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) (H' : allocPre row q' i S p) :
    rlCutAt row q' → rlCutAt row q := by
  rintro ⟨x, hL, hG⟩
  have hbq := AxSpinT2f.bDetBr (AxSpinT2f.brOf H) (AxSpinT2f.brOf H')
  rcases AxSpinT2f.rlPosGe x q' with rfl | hge
  · exact ⟨.poMy1, hL, hG⟩
  have C := AxSpinT2f.coreOfPre H
  have C' := AxSpinT2f.coreOfPre H'
  obtain ⟨b, hb, n, c⟩ := q
  obtain ⟨b', hb', n', c'⟩ := q'
  obtain rfl : b = b' := hbq (by omega)
  refine ⟨x, ?_⟩
  cases x <;> first
    | exact ⟨hL, hG⟩
    | (obtain rfl := AxSpinT2f.hbDet C C' (by rw [hL]; ax_spin_t2f_pos)
       first
         | exact ⟨hL, hG⟩
         | (obtain rfl := AxSpinT2f.nDet C C' (by rw [hL]; ax_spin_t2f_pos)
            first
              | exact ⟨hL, hG⟩
              | (obtain rfl := AxSpinT2f.cEq C C' (by rw [hL]; ax_spin_t2f_pos)
                 exact ⟨hL, hG⟩)))

/-! # 4. Bridges -/

/-- `graphValue` is the row value. -/
theorem AxSpinT2f.gvGrow (GD : Gdexec) (i k : Nat) :
    graphValue GD (i, k) = AxSpinT2f.rv (AxOpsem.grow GD i) k := by
  unfold graphValue gxLbl AxSpinT2f.rv AxOpsem.grow growG
  rcases GD.gdG.gxProg[i]? with _ | p <;> simp

/-- `graphData` is the row's write data. -/
theorem AxSpinT2f.wdGrow (GD : Gdexec) (i k : Nat) :
    graphData GD (i, k) = AxSpinT2f.wd (AxOpsem.grow GD i) k := by
  unfold graphData gxLbl AxSpinT2f.wd AxOpsem.grow growG
  rcases GD.gdG.gxProg[i]? with _ | p <;> simp

/-- A present row value sits at a present position. -/
theorem AxSpinT2f.rvLt {row : List Lbl} {k : Nat} {vs : List (BitVec 8)}
    (h : AxSpinT2f.rv row k = some vs) : k < row.length := by
  unfold AxSpinT2f.rv at h
  cases hk : row[k]? with
  | none => simp [hk] at h
  | some lb => exact (List.getElem?_eq_some_iff.1 hk).1

theorem AxSpinT2f.rdVal {lb : Lbl} {aq : Bool} {pa : Int} {n : Nat} :
    aident lb = .IRead aq pa n → ∃ vs, lblValue lb = some vs := by
  cases lb <;> simp [aident, lblValue]

/-- (Lean-only) a present 8-byte read item of a `RowShP` piece has a row value. -/
theorem AxSpinT2f.rdP {k j kr : Nat} {row : List Lbl} {sh : List Ritem} (P : RowShP k row sh)
    (hit : ∃ pa, sh[j]? = some (.RL pa 8)) (e : k + j = kr) (hk : kr < row.length) :
    ∃ vs, AxSpinT2f.rv row kr = some vs := by
  obtain ⟨pa, hit⟩ := hit
  subst e
  obtain ⟨lb, h1, aq, h2⟩ := rowShPAt P hit hk
  obtain ⟨vs, hv⟩ := AxSpinT2f.rdVal h2
  exact ⟨vs, by simp only [AxSpinT2f.rv, h1, Option.bind_some, hv]⟩

/-- (Lean-only) `rdP` for a `RowShXP` piece. -/
theorem AxSpinT2f.rdXP {k j kr : Nat} {row : List Lbl} {sh : List Rxitem} (P : RowShXP k row sh)
    (hit : ∃ pa, sh[j]? = some (.it (.RL pa 8))) (e : k + j = kr) (hk : kr < row.length) :
    ∃ vs, AxSpinT2f.rv row kr = some vs := by
  obtain ⟨pa, hit⟩ := hit
  subst e
  obtain ⟨lb, h1, aq, h2⟩ := P j _ hit hk
  obtain ⟨vs, hv⟩ := AxSpinT2f.rdVal h2
  exact ⟨vs, by simp only [AxSpinT2f.rv, h1, Option.bind_some, hv]⟩

/-- Every reload on the path that is present in a family row read a value (it is an 8-byte read
item of the shape). -/
theorem AxSpinT2f.rlRd {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) (x : T2Rj) (hon : rlOn x q = true)
    (hk : rlKr x q < row.length) : ∃ vs, AxSpinT2f.rv row (rlKr x q) = some vs := by
  obtain ⟨-, Ppo, Phd, -, Ptl, -, Prl, -⟩ := AxSpinT2f.segPartsP H.1
  obtain ⟨b, hb, n, c⟩ := q
  cases x with
  | poMy1 => exact AxSpinT2f.rdP Ppo (j := 5) (by cases b <;> exact ⟨_, rfl⟩) rfl hk
  | poMy2 =>
    simp only [rlOn] at hon
    subst hon
    exact AxSpinT2f.rdP Ppo (j := 10) ⟨_, rfl⟩ rfl hk
  | poMy3 =>
    cases b
    · exact AxSpinT2f.rdP Ppo (j := 10) ⟨_, rfl⟩ rfl hk
    · exact AxSpinT2f.rdP Ppo (j := 15) ⟨_, rfl⟩ rfl hk
  | poRet =>
    cases b
    · exact AxSpinT2f.rdP Ppo (j := 14) ⟨_, rfl⟩ rfl hk
    · exact AxSpinT2f.rdP Ppo (j := 19) ⟨_, rfl⟩ rfl hk
  | poS1 =>
    cases b
    · exact AxSpinT2f.rdP Ppo (j := 16) ⟨_, rfl⟩ rfl hk
    · exact AxSpinT2f.rdP Ppo (j := 21) ⟨_, rfl⟩ rfl hk
  | hdMy =>
    simp only [rlOn] at hon
    subst hon
    exact AxSpinT2f.rdP Phd (j := 7) ⟨_, rfl⟩ rfl hk
  | hdRet =>
    simp only [rlOn] at hon
    subst hon
    exact AxSpinT2f.rdP Phd (j := 9) ⟨_, rfl⟩ rfl hk
  | hdS1 =>
    simp only [rlOn] at hon
    subst hon
    exact AxSpinT2f.rdP Phd (j := 11) ⟨_, rfl⟩ rfl hk
  | aqMy => exact AxSpinT2f.rdP Ptl (j := 2) ⟨_, rfl⟩ rfl hk
  | aqRet => exact AxSpinT2f.rdP Ptl (j := 5) ⟨_, rfl⟩ rfl hk
  | aqS1 => exact AxSpinT2f.rdP Ptl (j := 7) ⟨_, rfl⟩ rfl hk
  | rhMy =>
    exact AxSpinT2f.rdXP Prl (j := 10) (by cases c <;> exact ⟨_, rfl⟩)
      (by ax_spin_t2f_pos) hk
  | rhRet =>
    exact AxSpinT2f.rdXP Prl (j := 12) (by cases c <;> exact ⟨_, rfl⟩)
      (by ax_spin_t2f_pos) hk
  | rhS1 =>
    exact AxSpinT2f.rdXP Prl (j := 14) (by cases c <;> exact ⟨_, rfl⟩)
      (by ax_spin_t2f_pos) hk
  | ppMy =>
    exact AxSpinT2f.rdXP Prl (j := 22) (by cases c <;> exact ⟨_, rfl⟩)
      (by ax_spin_t2f_pos) hk
  | ppRet =>
    cases c
    · exact AxSpinT2f.rdXP Prl (j := 27) ⟨_, rfl⟩ (by ax_spin_t2f_pos) hk
    · exact AxSpinT2f.rdXP Prl (j := 26) ⟨_, rfl⟩ (by ax_spin_t2f_pos) hk
  | rlRet =>
    cases c
    · exact AxSpinT2f.rdXP Prl (j := 29) ⟨_, rfl⟩
        (by ax_spin_t2f_pos) hk
    · exact AxSpinT2f.rdXP Prl (j := 28) ⟨_, rfl⟩
        (by ax_spin_t2f_pos) hk
  | rlS1 =>
    cases c
    · exact AxSpinT2f.rdXP Prl (j := 31) ⟨_, rfl⟩
        (by ax_spin_t2f_pos) hk
    · exact AxSpinT2f.rdXP Prl (j := 30) ⟨_, rfl⟩
        (by ax_spin_t2f_pos) hk

/-- push_off's branch bit from stage 1's `poArm` (and the shape). -/
theorem AxSpinT2f.brOfArm {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (HS : RowShXP 0 (AxOpsem.grow GD i) (allocSeg q i S p))
    (Harm : ∀ vn, graphValue GD (i, t2KPo + 7) = some vn → (ldRes false 4 vn == zero_reg) = q.b) :
    AxSpinT2f.poBranch (AxOpsem.grow GD i) q := by
  intro hl
  have P := (AxSpinT2f.segPartsP HS).2.1
  have hit : (poSh q.b (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
      (cpuZ i + 124))[7]? = some (.RL (cpuZ i + 120) 4) := by cases q.b <;> rfl
  obtain ⟨lb, h1, ⟨aq, h2⟩⟩ := rowShPAt P hit hl
  obtain ⟨vs, hv⟩ := AxSpinT2f.rdVal h2
  have hr : AxSpinT2f.rv (AxOpsem.grow GD i) (t2KPo + 7) = some vs := by
    simp only [AxSpinT2f.rv, h1, Option.bind_some, hv]
  exact ⟨vs, hr, Harm vs ((AxSpinT2f.gvGrow GD i _).trans hr)⟩

/-- `poArm` from the family (the selector is no longer a pin). -/
theorem AxSpinT2f.poArmOf {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p) :
    ∀ vn, graphValue GD (i, t2KPo + 7) = some vn → (ldRes false 4 vn == zero_reg) = q.b := by
  intro vn hv
  rw [AxSpinT2f.gvGrow] at hv
  obtain ⟨vs, h1, h2⟩ := AxSpinT2f.brOf H (AxSpinT2f.rvLt hv)
  rw [h1] at hv
  cases hv
  exact h2

/-- A FULL row with the panic / `intr_on` gates, push_off's branch bit and the reload gates is in
the prefix family. -/
theorem preOfFull {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (HF : allocFull row q i S p) (HG : ∀ j, t2GateOk j row q i) (HB : AxSpinT2f.poBranch row q)
    (HR : ∀ x, rlGateOk x row q) : allocPre row q i S p := by
  obtain ⟨H1, H2, H3, H4, -, H6, H7, H8, H9⟩ := HF
  exact ⟨rowShXPOfX H1, by omega, fun _ => H3, AxSpinT2f.spinValsPOf H4, ⟨H6.2.1, H6.2.2⟩,
    fun j hj _ => H7 j hj, H8, H9, fun j _ => HG j, HB, fun x _ => HR x⟩

/-- Stage 1's pins (and `allocFull`'s release lock bit) give the five panic / `intr_on` gates. -/
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

/-- Stage 1's (unguarded) reload pins give every reload gate. -/
theorem AxSpinT2f.rlGatesOfPins {GD : Gdexec} {i : Agent} {q : T2Prm} (HP : AllocPins GD i q) :
    ∀ x, rlGateOk x (AxOpsem.grow GD i) q := by
  intro x hon vs hv
  have G := (AxSpinT2f.gvGrow GD i (rlKr x q)).trans hv
  cases x with
  | poMy1 => exact HP.poMy1.symm.trans G
  | poMy2 => exact (HP.poMy2 hon).symm.trans G
  | poMy3 => exact HP.poMy3.symm.trans G
  | poRet => exact HP.poRet.symm.trans G
  | poS1 => exact HP.poS1.symm.trans G
  | hdMy => exact (HP.hdRets hon).1.symm.trans G
  | hdRet => exact (HP.hdRets hon).2.symm.trans G
  | hdS1 => exact (HP.hdS1 hon).symm.trans G
  | aqMy => exact HP.aqMy.symm.trans G
  | aqRet => exact HP.aqRet.symm.trans G
  | aqS1 => exact (AxSpinT2f.wdGrow GD i 2).symm.trans (HP.aqS1.symm.trans G)
  | rhMy => exact HP.rhRets.1.symm.trans G
  | rhRet => exact HP.rhRets.2.symm.trans G
  | rhS1 => exact HP.rhS1.symm.trans G
  | ppMy => exact HP.ppMy.symm.trans G
  | ppRet => exact HP.ppRet.symm.trans G
  | rlRet => exact HP.rlRet.symm.trans G
  | rlS1 => exact (AxSpinT2f.wdGrow GD i _).symm.trans (HP.rlS1.symm.trans G)

/-- Stage 1's family + pins ⇒ the prefix family. -/
theorem preOfFullPins {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (HF : allocFull (AxOpsem.grow GD i) q i S p) (HP : AllocPins GD i q) :
    allocPre (AxOpsem.grow GD i) q i S p :=
  preOfFull HF (AxSpinT2f.gatesOfPins HF HP) (AxSpinT2f.brOfArm (rowShXPOfX HF.1) HP.poArm)
    (AxSpinT2f.rlGatesOfPins HP)

/-- A family row of FULL length is a stage-1 family row. -/
theorem fullOfPre {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) (hl : row.length = t2Len q) : allocFull row q i S p := by
  obtain ⟨H1, -, H3, H4, H5, H6, H7, H8, H9, -, -⟩ := H
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
    (HG : ∀ q, allocFull (AxOpsem.grow GD i) q i S p →
      (∀ j, t2GateOk j (AxOpsem.grow GD i) q i) ∧ AxSpinT2f.poBranch (AxOpsem.grow GD i) q ∧
        ∀ x, rlGateOk x (AxOpsem.grow GD i) q) :
    t2Complete GD i S p ↔
      ∃ q, allocPre (AxOpsem.grow GD i) q i S p ∧ (AxOpsem.grow GD i).length = t2Len q := by
  constructor
  · rintro ⟨q, HF⟩
    obtain ⟨G1, G2, G3⟩ := HG q HF
    exact ⟨q, preOfFull HF G1 G2 G3, HF.2.1⟩
  · rintro ⟨q, H, hl⟩
    exact ⟨q, fullOfPre H hl⟩

/-- A COMPLETE row fixes the family parameters (push_off's arm, holding's lock bit, the spins,
pop_off's arm). -/
theorem AxSpinT2f.qEqFull {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : AxSpinT2f.preCore row q i S p) (HF : allocFull row q' i S p) : q = q' := by
  have C' := AxSpinT2f.coreOfFull HF
  have hl : row.length = t2Len q' := HF.2.1
  have hb := by
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs q'
    exact AxSpinT2f.bDet H C' (by omega)
  obtain ⟨b, hb0, n, c⟩ := q
  obtain ⟨b', hb', n', c'⟩ := q'
  simp only at hb
  subst hb
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := AxSpinT2f.kEqs ⟨b, hb', n', c'⟩
  dsimp only at k1 k2 k3 k4 k5 k6 k7 k8 k9
  have e1 : t2KHd ⟨b, hb0, n, c⟩ = t2KHd ⟨b, hb', n', c'⟩ := rfl
  have hhb := AxSpinT2f.hbDet H C' (by omega)
  subst hhb
  have hn := AxSpinT2f.nDet H C' (by omega)
  subst hn
  have e2 : t2KPp ⟨b, hb0, n, c⟩ = t2KPp ⟨b, hb0, n, c'⟩ := rfl
  cases c' with
  | false =>
    rw [AxSpinT2f.cDet H C' (by omega)]
  | true =>
    cases c with
    | true => rfl
    | false => exact absurd (AxSpinT2f.cDet C' H (by omega)) (by decide)

/-- DETERMINACY on family rows (panic / `intr_on` part: `cutDetCore`; reload part: `rlDet`). -/
theorem cutDet {row : List Lbl} {q q' : T2Prm} {i : Agent} {S p : Int}
    (H : allocPre row q i S p) (H' : allocPre row q' i S p) :
    t2CutAt row q' i → t2CutAt row q i :=
  Or.imp (AxSpinT2f.cutDetCore (AxSpinT2f.coreOfPre H) (AxSpinT2f.coreOfPre H'))
    (AxSpinT2f.rlDet H H')

/-- A row ending at no designated position (panic / `intr_on` or reload) is not a cut row. -/
theorem notCutAtOfLen {row : List Lbl} {q : T2Prm} {i : Agent}
    (h : ∀ j, row.length ≠ cutPos j q) (hr : ∀ x, row.length ≠ rlPos x q) : ¬ t2CutAt row q i := by
  rintro (⟨j, hL, -⟩ | ⟨x, hL, -⟩)
  · exact h j hL
  · exact hr x hL

/-- A row whose end gates (panic / `intr_on` and reload, if any) took the normal arm is not a cut
row. -/
theorem notCutAtOfGates {row : List Lbl} {q : T2Prm} {i : Agent}
    (h : ∀ j, row.length = cutPos j q → t2GateOk j row q i)
    (hr : ∀ x, row.length = rlPos x q → rlGateOk x row q) : ¬ t2CutAt row q i := by
  rintro (⟨j, hL, hG⟩ | ⟨x, hL, hG⟩)
  · exact hG (h j hL)
  · exact hG (hr x hL)

/-- `¬ t2Cut` from the q-indexed fact (what the WPd proves for the premise's `q`). -/
theorem notCutOfGates {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p)
    (h : ∀ j, (AxOpsem.grow GD i).length = cutPos j q → t2GateOk j (AxOpsem.grow GD i) q i)
    (hr : ∀ x, (AxOpsem.grow GD i).length = rlPos x q → rlGateOk x (AxOpsem.grow GD i) q) :
    ¬ t2Cut GD i S p := by
  rintro ⟨q', H', Hc⟩
  exact notCutAtOfGates h hr (cutDet H H' Hc)

/-- Pure `¬ t2Cut` at a row end that is neither a panic / `intr_on` nor a reload position. -/
theorem notCutOfLen {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p)
    (h : ∀ j, (AxOpsem.grow GD i).length ≠ cutPos j q)
    (hr : ∀ x, (AxOpsem.grow GD i).length ≠ rlPos x q) : ¬ t2Cut GD i S p :=
  notCutOfGates H (fun j hL => absurd hL (h j)) (fun x hL => absurd hL (hr x))

/-- A complete (stage-1 family) row is no cut row. -/
theorem cutNotFull {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (HF : allocFull (AxOpsem.grow GD i) q i S p) : ¬ t2Cut GD i S p := by
  rintro ⟨q', H', Hc⟩
  have e := AxSpinT2f.qEqFull (AxSpinT2f.coreOfPre H') HF
  have hl := HF.2.1
  rw [← e] at hl
  rcases Hc with ⟨j, hL, -⟩ | ⟨x, hL, -⟩
  · have := AxSpinT2f.cutPosLen j q'
    omega
  · have := AxSpinT2f.rlPosLen x q'
    omega

theorem AxSpinT2f.notCutOfComplete {GD : Gdexec} {i : Agent} {S p : Int} :
    t2Complete GD i S p → ¬ t2Cut GD i S p :=
  fun ⟨_, HF⟩ => cutNotFull HF

/-! # 5. The guarded pins -/

/-- Stage 1's `AllocPins` MINUS the five panic / `intr_on` arm pins (`hdArm`, `rhArm`, `rhCpu`,
`ppGe`, `ppInt`), the 18 RELOAD pins (now `allocPre`'s reload gates) and the selector `poArm`
(now `allocPre`'s `poBranch`; `AxSpinT2f.poArmOf`).  Kept: the Q18b scope pins, the selector
`ppArm`, and the INTERIM row-end reload premise `rlEnd` (see the header, §5). -/
structure AllocPins2 (GD : Gdexec) (i : Agent) (q : T2Prm) : Prop where
  /-- Q18b: the nextpid read is not 1000 and does not wrap -/
  npNowrap : ∀ vs, graphValue GD (i, t2KBd q) = some vs →
    (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32
  /-- Q18b: no pid collision in the scan -/
  npNcoll : ∀ vs, graphValue GD (i, t2KBd q) = some vs → ∀ j, j < 64 → ∀ v,
    graphValue GD (i, t2KBd q + 1 + j) = some v → (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs
  /-- pop_off's arm `c` -/
  ppArm : ∀ vn, graphValue GD (i, t2KPp q + 6) = some vn →
    (addiwm1 (ldRes false 4 vn) != zero_reg) = q.c
  /-- INTERIM (until the leaf lanes take `AxSpinT2i.Gate`): a row that ENDS right after a
  reload read the spill there (vacuous unless `LEN = rlPos x q`) -/
  rlEnd : ∀ x, (AxOpsem.grow GD i).length = rlPos x q → rlGateOk x (AxOpsem.grow GD i) q

/-- Stage 1's pins give the guarded ones. -/
theorem pins2OfPins {GD : Gdexec} {i : Agent} {q : T2Prm} (HP : AllocPins GD i q) :
    AllocPins2 GD i q where
  npNowrap := HP.npNowrap
  npNcoll := HP.npNcoll
  ppArm := HP.ppArm
  rlEnd x _ := AxSpinT2f.rlGatesOfPins HP x

/-- `¬ reloadMis` from the interim premise `rlEnd` (the q-indexed reload part). -/
theorem AxSpinT2f.notRlCutOf {GD : Gdexec} {i : Agent} {q : T2Prm} (HP : AllocPins2 GD i q) :
    ¬ rlCutAt (AxOpsem.grow GD i) q :=
  fun ⟨x, hL, hG⟩ => hG (HP.rlEnd x hL)

/-- THE BRIDGE for the leaf P-forms that still take guarded pins: `allocPre`'s reload gate (the
row continues past the reload) and `rlEnd` (it ends right after it) give the old guarded pin
`kr < LEN → graphValue (i, kr) = expected`. -/
theorem AxSpinT2f.pinOf {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p) (HP : AllocPins2 GD i q) (x : T2Rj)
    (hon : rlOn x q = true) :
    rlKr x q < (AxOpsem.grow GD i).length →
      graphValue GD (i, rlKr x q) = rlExp x (AxOpsem.grow GD i) q := by
  intro hk
  obtain ⟨vs, hv⟩ := AxSpinT2f.rlRd H x hon hk
  have G : rlGateOk x (AxOpsem.grow GD i) q := by
    by_cases h : rlPos x q < (AxOpsem.grow GD i).length
    · exact AxSpinT2f.rlGatesOf H x h
    · exact HP.rlEnd x (by unfold rlPos at h ⊢; omega)
  rw [AxSpinT2f.gvGrow, hv]
  exact (G hon vs hv).symm

/-- `pinOf` for the two spill-data reloads, in stage 1's `graphData` form. -/
theorem AxSpinT2f.pinOfD {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p) (HP : AllocPins2 GD i q) :
    (t2KMy q + 7 < (AxOpsem.grow GD i).length →
      graphValue GD (i, t2KMy q + 7) = graphData GD (i, 2)) ∧
    (t2KRr q + 2 < (AxOpsem.grow GD i).length →
      graphValue GD (i, t2KRr q + 2) = graphData GD (i, t2KRl q + 2)) :=
  ⟨fun hk => (AxSpinT2f.pinOf H HP .aqS1 rfl hk).trans (AxSpinT2f.wdGrow GD i 2).symm,
   fun hk => (AxSpinT2f.pinOf H HP .rlS1 rfl hk).trans (AxSpinT2f.wdGrow GD i _).symm⟩

/-- The GATE form for the leaf lanes: exactly the body of `AxSpinT2i.Gate GT i (rlKr x q) vw` at
`GD = gtAdGd GT` ("a row that continues past the reload read the spill"), from `allocPre` alone
(no pin). -/
theorem AxSpinT2f.gateBody {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int} {x : T2Rj}
    {vw : List (BitVec 8)} (H : allocPre (AxOpsem.grow GD i) q i S p) (hon : rlOn x q = true)
    (hexp : rlExp x (AxOpsem.grow GD i) q = some vw) :
    graphValue GD (i, rlKr x q) ≠ some vw → (AxOpsem.grow GD i).length ≤ rlKr x q + 1 := by
  intro hne
  refine Nat.le_of_not_lt fun hl => ?_
  obtain ⟨vs, hv⟩ := AxSpinT2f.rlRd H x hon (by omega)
  have E := AxSpinT2f.rlGatesOf H x hl hon vs hv
  rw [hexp] at E
  cases E
  exact hne (by rw [AxSpinT2f.gvGrow]; exact hv)

/-! # 6. The noff image premise -/

/-- `cpus[cpuOf i].noff`'s image bytes hold the 32-bit word `v`, `0 ≤ v < 2^31 − 1`. -/
def noffImgOk (img : Image) (i : Agent) (v : Int) : Prop :=
  0 ≤ v ∧ v < 2 ^ 31 - 1 ∧
  ∀ (j : Nat) (b : BitVec 8), (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v))[j]? = some b →
    img (cpuZ i + 120 + j) = some b

/-- The design's `Himgnoff` (scope premise Q-S2-3), for harts A and B. -/
def HimgNoff (img : Image) (A B : Agent) : Prop := ∀ i, i ∈ [A, B] → ∃ v, noffImgOk img i v

end Weak
