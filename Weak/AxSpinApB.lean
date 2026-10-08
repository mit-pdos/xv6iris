/-
Weak: **THEOREM 2, STAGE 2, row `AxSpinApA (edit/new ApB)` — THE WHOLE SEGMENT ON PREFIX ROWS**
(stage-2 design `notes/weak-lb-thm2-stage2.md` §A, §B, §C row `AxSpinApA (edit/new ApB)`; Q-S2-1/2).
NEW Lean file (no Rocq source; Rocq's ID-8 prefix family is the model).  `AxSpinApA` is NOT edited:
`wpdAllocpidSeg`, `wpdAllocpidSegS`, `AxSpinApA.wpdAllocpidSegE` keep their names and statements.

## What this file proves

§1 ROW FACTS OF THE PREFIX FAMILY (`allocPre`, AxSpinT2f).  `AxSpinApB.itemP` (every PRESENT row
   item matches its `allocSeg` item); `w8P`/`rmwP`/`noRmwnP`/`noRmw8P` (stage 1's `allocW8`/… on
   prefixes); THE WRITES BY POSITION `AxSpinApB.segWrP` — `AxSpinApA.segWr` restated on prefixes and
   REFINED: the cpu-field stores are located (`AxSpinApB.WrAtP`: push_off's `sw noff` at
   `t2KPoT q + 5`, pop_off's at `t2KPp q + 7`, push_off's `sw intena` at `t2KPo + 12` on the arm
   `q.b`; `poShW`/`ppShW` enumerate the two windows); its consequences `npOnlyP`, `npBeforeP`,
   `lkBetweenP`, `clbBetweenP`, `clbBefore` (no own `lk->cpu` write before acquire's racy read:
   `cutAq`'s `Hns`), `wle4P`, `relWinCP`, and the three facts the D4 readback of the noff arms
   needs: `noffNoWrB` (push_off's two noff loads read the IMAGE: the genesis annotations'
   `noWrBefore`), `noffNowr` / `intenaNowr` (no write to noff / intena between push_off's store and
   pop_off's reload: the `rlOk4` `nowr` of pop_off's optional reloads).  `acqP` (acquire's
   `RowAcquireP`), `holdP`, `cpuWinP`, `gateRlSOf`, `notCutAt`, `rdOfP`/`rdOfXP`/`gvRd`/`st8`.
§2 `AxSpinApB.Hyp2` — `AxSpinApA.Hyp` with `allocPre`, the GUARDED pins `AllocPins2` and the noff
   image premise (`∃ v, noffImgOk img i v`, the hart's instance of `HimgNoff`, Q-S2-3); the
   bundle lemmas `dat`/`hitStk`/`slot`/`fld`/`ntxOf` re-stated on it.
§3 THE POST `AxSpinApB.t2PostP GD L nm i q s` := `⌜¬ midState s⌝ -∗ ⌜¬ t2CutAt (grow GD i) q i⌝ ∗
   (⌜LEN = t2Len q⌝ -∗ ∃ w, ⌜pidOf = wbytes 4 w ∧ npSrc⌝ ∗ FRAG nm w)` (= `t2PostS` + the cut
   conjunct; complete rows give the stage-1 post).  `postP` (free at an incomplete no-cut end),
   `postCut` (free at a designated cut whose gate took the normal arm), `postSMidP`.
   ROW ENDS: `AxSpinApB.wpdPast` — from `k0 ≥ LEN`, `WPd ⟨pr, k0⟩ Φ` for a PURE post demanded only
   when `k0 = LEN` (past the row end every step is administrative and keeps the position, so the
   row-end clause is never reached when `k0 > LEN`); `AxSpinApB.hookP` — THE RESOURCE-FREE HOOK
   (Q-S2-2) every P-form's `HΨend` is instantiated with: at `k' < t2Len q`, `LEN ≤ k'`, unless `k'`
   is a designated cut (`aq` only when `hb`, `rlS` unless its gate is known, `rlL`, `ppN`, `ppI`
   only when `c = false`).  NOTE: the hooks are stated with `LEN ≤ k'` (not `=`), so `wpdPast` is
   what makes them provable for `t2PostP` (a row shorter than `k'` may end at a flipped cut).
§4 THE PIECES on prefix rows (all `Ψ := t2PostP`):
   `AxSpinApB.segRelP` — `jal release` → `wpdReleaseP` (holding's lock bit `hbR` READ OFF THE ROW:
     the `lw` value if present, `false` only at the `rlS` cut by the gate conjunct of `allocPre`)
     with the four designated arms `KrlS ← cutRelS`, `KrlL ← cutRelL`, `KppN ← cutPpNF`,
     `KppI ← cutPpIF` (push_off's two genesis annotations `AxSpinT2h.genF` as the FRAME), pop_off's
     reloads `rlN := some (sw noff)`, `rlI := if q.b then some (sw intena) else none` (labels from
     `KAcqP`), → `c.li` → the terminal store; continuation at `t2Len q` with `LEN = t2Len q`;
   `AxSpinApB.segCsP` — `wpdAllocpidCsP` (window without cuts) → `segRelP`; at the complete end the
     `npSrc` / `FRAG` annotations are read back (`AxSpinApA.wpdEnd2`);
   **`wpdAllocpidSeg2`** — `auipc`/`addi`/`jal acquire` → `AxSpinAq2.wpdAcquireP` (cut `aq` ←
     `cutAq`; the non-panic arm pin past the cut from `allocPre`'s gate; `KAcqP`'s genesis
     annotations discharged by `noffNoWrB`) → `segCsP`:
       `isLock … -∗ notheld i -∗ WPd ⟨rs0, 0⟩ {{ t2PostP (gtAdGd GT) L nm i q }}`.
§5 `AxSpinApB.wpdAllocpidSeg2E` (from `entryOk`), `AxSpinApB.hypXv6P` (`Hyp2` at `xlayXv6`, from
   `allocPre`, `AllocPins2`, `HimgNoff`), `AxSpinApB.hyp2OfHyp` (stage 1's bundle → stage 2's),
   `AxSpinApB.notCutOfAt` (the q-indexed cut conjunct → the design's `¬ t2Cut`, via `cutDet`).

## Deviations from the design / honesty / open points

1. **OWNER QUESTION Q-S2-B OPEN (byte mixing).**  `wpdAllocpidSeg2` carries `cutAq`'s explicit,
   named premise `HsrcAl : AxSpinT2g.clSrcAligned (clb L) G (i, t2KHd q + 4)` (AxSpinT2h deviation
   1).  Two more explicit graph premises come with `cutAq`: `Himgc` (the `lk->cpu` image is 0, as
   stage 1's capstone premise) and `Hwlt` (writers of `lk->cpu` are harts `< NCPU`,
   `AxSpinT2g`'s writer lemma supplies it from the gmo).
2. The post is q-INDEXED (`t2CutAt row q i`, `LEN = t2Len q`) rather than the design's
   `¬ t2Cut GD i` / `t2Complete GD i`; `notCutOfAt` (+ `cutDet`) and `fullOfPre` are the bridges
   (AxSpinT2f deviation 2: `t2Cut` quantifies `q` inside the family).
3. The `a3` conjunct is not in the post (as stage 1: `AxSpinApA` FINDING, `PROGRESS-AxSpinApA.md`).
4. Pins: exactly `AllocPins2` (guarded; Option V reload pins, Q18b, the selectors `poArm`/`ppArm`,
   all hart `i`'s own reads).  `hdArm`/`rhArm`/`rhCpu`/`ppGe`/`ppInt` and release's lock bit are
   NOT premises: on the normal arm they come from `allocPre`'s gate conjunct, at the cut they are
   refuted by D4 readback (AxSpinT2h).  The theorem proves nothing about a graph whose pinned
   values differ.  Prefix closure stays informal (design §B, Q-S2-6).
5. pop_off's own spills' `nowr` is discharged inside `wpdPopOffP` (AxSpinPO6.rowShPNowr); what
   this file discharges are the `nowr` of pop_off's two optional RELOADS (`noffNowr`,
   `intenaNowr`) and the genesis `noWrBefore` of push_off's two noff loads (`noffNoWrB`).

**Reused:** `wpdAcquireP`/`KAcqP` (AxSpinAq2), `wpdAllocpidCsP`/`RowAllocpidBodyP` (AxSpinAp9),
`wpdReleaseP` (AxSpinRl4b, with the frame), `cutAq`/`cutRelS`/`cutRelL`/`cutPpNF`/`cutPpIF`/
`genF`/`gateAq`/`gateRlS`/`gateRlL`/`gatePpN`/`gatePpI`/`RdAt`/`ldOfRd`/`stBytes4Len` (AxSpinT2h),
`allocPre`/`AllocPins2`/`noffImgOk`/`HimgNoff`/`cutPos`/`t2GateOk`/`t2CutAt`/`segPartsP`/`kEqs`/
`cutPosLen`/`cutPosInj`/`gvGrow`/`rdVal`/`notCutAtOfGates`/`notCutAtOfLen`/`cutDet`/
`preOfFullPins`/`pins2OfPins` (AxSpinT2f), `AxSpinApA.*` (`WrAt`, `xWmOf`, `appCase`, `mapW`,
`itRS`, `aqTailW`, `bodyW`, `get3`, `nums`, `Lay`, `MapOk`, `Warm`, address lemmas, `annotEntailX`,
`sepTrue`, `wpdEnd2`, `rowEndShape`, `FstMPriv`, `tailText` tokens), `AxSpinRl4.rowHoldingPOf`/
`gvLt`, `AxSpinRl2.lobpAcq`/`lobpCpuSt`/`lobpCpuLd`/`stBytes8`, `AxSpinT2a.*` (`segB`, `itB`, `xB`,
`mycpuRetHart`, `hresZero`, `jalrRets`, `hartLt`, `privIff`, `symV`, `kBdLen`, `kSpA`),
`postLiftingTrue`, `AxWpD.wpdMUnfoldStep`, `progressOblMaybestuck`, `shSkip`, `AxSpinWit.gconstEq`.
**New names:** `wpdAllocpidSeg2` (unqualified, grepped absent); everything else `AxSpinApB.*`
(+ 3 local macros).
-/
import Weak.AxSpinApA
import Weak.AxSpinT2h

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The prefix family's row facts -/

/-- push_off's window: which items write, and where (the two cpu-field stores by index). -/
theorem AxSpinApB.poShW {b : Bool} {pra ps0 ps1 pmra pms0 pn pint bb : Int} {j m : Nat}
    (h : (poSh b pra ps0 ps1 pmra pms0 pn pint)[j]? = some (Ritem.RS bb m)) :
    (bb = pn ∧ m = 4 ∧ j = 13 + (if b then 5 else 0)) ∨
    (bb = pint ∧ m = 4 ∧ b = true ∧ j = 12) ∨
    ((bb = pra ∨ bb = ps0 ∨ bb = ps1 ∨ bb = pmra ∨ bb = pms0) ∧ m = 8) := by
  cases b <;>
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | j <;>
    simp [poSh, poHead, poInt, poTail, mycSh] at h ⊢ <;> omega

/-- pop_off's window: which items write, and where (the noff store by index). -/
theorem AxSpinApB.ppShW {c : Bool} {qra qs0 qmra qms0 pn pint bb : Int} {j m : Nat}
    (h : (ppSh c qra qs0 qmra qms0 pn pint)[j]? = some (Ritem.RS bb m)) :
    (bb = pn ∧ m = 4 ∧ j = 7) ∨ ((bb = qra ∨ bb = qs0 ∨ bb = qmra ∨ bb = qms0) ∧ m = 8) := by
  cases c <;>
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [ppSh, ppHead, ppMid, ppTail, mycSh] at h ⊢ <;> omega

/-- THE WRITES OF THE PREFIX FAMILY BY POSITION (`AxSpinApA.WrAt` with the two cpu fields'
stores located: push_off's `sw noff` at `t2KPoT q + 5`, pop_off's at `t2KPp q + 7`, push_off's
`sw intena` at `t2KPo + 12` on the arm `q.b`). -/
def AxSpinApB.WrAtP (q : T2Prm) (i : Agent) (S p : Int) (k : Nat) (b : Int) (m : Nat) : Prop :=
  (m = 8 ∧ S - 80 ≤ b ∧ b + 8 ≤ S) ∨
  (m = 4 ∧ ((b = cpuZ i + 120 ∧ (k = t2KPoT q + 5 ∨ k = t2KPp q + 7)) ∨
    (b = cpuZ i + 124 ∧ q.b = true ∧ k = t2KPo + 12))) ∨
  (m = 4 ∧ b = AxSpinT2a.zLk ∧ ((t2KSp q ≤ k ∧ k ≤ t2KA q) ∨ k = relKw (t2KRl q))) ∨
  (m = 8 ∧ b = AxSpinT2a.zLk + 16 ∧ (k = t2KMy q + 4 ∨ k = relKc (t2KRl q))) ∨
  (m = 4 ∧ b = AxSpinT2a.zNp ∧ k = t2KBd q + 65) ∨
  (m = 4 ∧ (b = p + 48 ∨ b = p + 24))

theorem AxSpinApB.wrAtOfP {q : T2Prm} {i : Agent} {S p : Int} {k : Nat} {b : Int} {m : Nat} :
    AxSpinApB.WrAtP q i S p k b m → AxSpinApA.WrAt q i S p k b m := by
  rintro (h | ⟨hm, (⟨hb, -⟩ | ⟨hb, -⟩)⟩ | h | h | h | h)
  · exact .inl h
  · exact .inr (.inl ⟨hm, .inl hb⟩)
  · exact .inr (.inl ⟨hm, .inr hb⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr h))))

/-- (Lean-only) the position facts `omega` needs (as `AxSpinApA.posFacts`). -/
theorem AxSpinApB.posF (q : T2Prm) :
    t2KSp q ≤ t2KA q ∧ t2KA q + 1 = t2KMy q ∧ t2KBd q = t2KMy q + 8 ∧
    t2KRl q = t2KBd q + 67 ∧ t2KRh q = t2KRl q + 3 ∧ relKc (t2KRl q) = t2KRl q + 15 ∧
    relKw (t2KRl q) = t2KRl q + 17 ∧ t2KPp q = t2KRl q + 18 ∧ t2KPoT q + 9 = t2KHd q ∧
    t2KMy q = t2KSp q + q.n + 1 := by
  refine ⟨Nat.le_add_right _ _, AxSpinT2a.kAEq q, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold t2KPoT t2KPo; rw [AxSpinT2a.kHdEq]; omega
  · simp only [t2KMy, t2KSp, aqKm]; omega

section pre
variable {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
variable (Hpre : allocPre row q i S p)
include Hpre

/-- every PRESENT row item matches its segment item (`allocItem` on prefixes). -/
theorem AxSpinApB.itemP (k : Nat) (lb : Lbl) :
    row[k]? = some lb → ∃ x, (allocSeg q i S p)[k]? = some x ∧ xshape x lb := by
  intro Hk
  have Hlt0 := (List.getElem?_eq_some_iff.1 Hk).1
  have Hlt : k < (allocSeg q i S p).length := by rw [allocSegLen]; have := Hpre.2.1; omega
  obtain ⟨x, Hx⟩ : ∃ x, (allocSeg q i S p)[k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
  obtain ⟨lb', Hlb', Hs⟩ := Hpre.1 k x Hx (by omega)
  rw [Nat.zero_add, Hk] at Hlb'
  cases Hlb'
  exact ⟨x, Hx, Hs⟩

/-- `allocW8` on prefixes. -/
theorem AxSpinApB.w8P : rowW8 row := by
  intro k lb rl b m Hk Hw
  obtain ⟨x, Hx, Hs⟩ := AxSpinApB.itemP Hpre k lb Hk
  have HB := AxSpinT2a.segB q i S p x (List.mem_of_getElem? Hx)
  cases x with
  | it it =>
    cases it with
    | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hw; cases Hw
    | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RS pb n =>
      obtain ⟨vw, cls, rfl, Hl⟩ := Hs
      simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
      obtain ⟨_, _, rfl⟩ := Hw
      simp only [AxSpinT2a.xB, AxSpinT2a.itB, decide_eq_true_eq] at HB
      omega
  | RB pr pw sr sw => rw [Hs] at Hw; cases Hw
  | RSc pb n cls =>
    obtain ⟨vw, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, _, rfl⟩ := Hw
    simp only [AxSpinT2a.xB, decide_eq_true_eq] at HB
    omega
  | RM aq rl' pb n =>
    rw [Hs] at Hw
    simp only [aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, _, rfl⟩ := Hw
    simp only [AxSpinT2a.xB, Bool.and_eq_true, decide_eq_true_eq] at HB
    omega

/-- `allocRmw` on prefixes. -/
theorem AxSpinApB.rmwP (k : Nat) (lb : Lbl) (aq rl : Bool) (pa : Int) (m : Nat) :
    row[k]? = some lb → aident lb = .IRmw aq rl pa m → pa = AxSpinT2a.zLk ∧ m = 4 := by
  intro Hk Hid
  obtain ⟨x, Hx, Hs⟩ := AxSpinApB.itemP Hpre k lb Hk
  have HB := AxSpinT2a.segB q i S p x (List.mem_of_getElem? Hx)
  cases x with
  | it it =>
    cases it with
    | RF n => obtain ⟨aq', b', E⟩ := Hs; rw [E] at Hid; cases Hid
    | RP pb n => obtain ⟨aq', E⟩ := Hs; rw [E] at Hid; cases Hid
    | RL pb n => obtain ⟨aq', E⟩ := Hs; rw [E] at Hid; cases Hid
    | RS pb n => obtain ⟨vw, cls, rfl, -⟩ := Hs; cases Hid
  | RB pr pw sr sw => rw [Hs] at Hid; cases Hid
  | RSc pb n cls => obtain ⟨vw, rfl, -⟩ := Hs; cases Hid
  | RM aq' rl' pb n =>
    rw [Hs] at Hid
    cases Hid
    simp only [AxSpinT2a.xB, Bool.and_eq_true, decide_eq_true_eq] at HB
    exact HB

theorem AxSpinApB.noRmwnP (pa : Int) (n : Nat) (h : pa ≠ AxSpinT2a.zLk ∨ n ≠ 4) :
    noRmwn row pa n := by
  intro k lb aq rl m Hk Hid
  obtain ⟨h1, h2⟩ := AxSpinApB.rmwP Hpre k lb aq rl pa m Hk Hid
  rcases h with h | h
  · exact absurd h1 h
  · omega

theorem AxSpinApB.noRmw8P (pa : Int) : noRmw8 row pa :=
  AxSpinApB.noRmwnP Hpre pa 8 (.inr (by decide))

/-- THE WRITES OF THE PREFIX FAMILY, BY POSITION (`AxSpinApA.segWr` on prefixes, with the
cpu-field stores located). -/
theorem AxSpinApB.segWrP (k : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    row[k]? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    AxSpinApB.WrAtP q i S p k b m := by
  intro Hk Hw
  obtain ⟨x, Hx, Hs⟩ := AxSpinApB.itemP Hpre k lb Hk
  have Hxw := AxSpinApA.xWmOf x lb rl b m Hs Hw
  unfold AxSpinApB.WrAtP
  unfold allocSeg at Hx
  rcases AxSpinApA.appCase Hx with ⟨h0, H⟩ | ⟨h0, H⟩
  · -- acquire's spills
    have := AxSpinApA.mapW H Hxw
    refine Or.inl ?_
    clear Hx H Hk Hs Hxw Hpre
    simp only [aqHead, List.mem_cons, List.not_mem_nil, or_false, Ritem.RS.injEq] at this
    omega
  rw [List.length_map, AxSpinT2a.aqHeadLen] at h0 H
  rcases AxSpinApA.appCase H with ⟨h1, H⟩ | ⟨h1, H⟩
  · -- push_off (the two cpu-field stores by position)
    rw [List.getElem?_map] at H
    obtain ⟨it, Hit, rfl⟩ := Option.map_eq_some_iff.1 H
    rw [AxSpinApA.itRS Hxw] at Hit
    have hpo : t2KPoT q = 11 + (if q.b then 5 else 0) := by unfold t2KPoT t2KPo; omega
    rcases AxSpinApB.poShW Hit with ⟨rfl, rfl, hj⟩ | ⟨rfl, rfl, hb, hj⟩ | ⟨hs, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, .inl ⟨rfl, .inl (by omega)⟩⟩)
    · exact Or.inr (Or.inl ⟨rfl, .inr ⟨rfl, hb, by unfold t2KPo; omega⟩⟩)
    · exact Or.inl ⟨rfl, by omega, by omega⟩
  rw [List.length_map, AxSpinT2a.poShLen] at h1 H
  rcases AxSpinApA.appCase H with ⟨h2, H⟩ | ⟨h2, H⟩
  · -- holding
    have := AxSpinApA.mapW H Hxw
    refine Or.inl ?_
    clear Hx H Hk Hs Hxw h0 h1 h2 Hpre
    cases hb : q.hb <;>
      simp only [hb, holdShB, mycSh, ↓reduceIte, Bool.false_eq_true,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, Ritem.RS.injEq, false_or] at this <;>
      omega
  rw [List.length_map, holdShBLen] at h2 H
  rcases AxSpinApA.appCase H with ⟨h3, H⟩ | ⟨h3, H⟩
  · -- the spins
    rw [List.length_replicate] at h3
    rw [List.getElem?_replicate, if_pos h3] at H
    cases H
    simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq] at Hxw
    obtain ⟨rfl, rfl⟩ := Hxw
    have e1 : t2KSp q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb := by
      simp only [t2KSp, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;> simp
    have e2 : t2KA q = t2KSp q + q.n := rfl
    refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inl ⟨?_, ?_⟩⟩))
    · rw [e1]; omega
    · rw [e2, e1]; omega
  rw [List.length_replicate] at h3 H
  rcases AxSpinApA.appCase H with ⟨h4, H⟩ | ⟨h4, H⟩
  · -- acquire's tail
    rw [List.length_map, aqTailLen] at h4
    rw [List.getElem?_map] at H
    obtain ⟨it, Hit, rfl⟩ := Option.map_eq_some_iff.1 H
    rw [AxSpinApA.itRS Hxw] at Hit
    have hk : t2KMy q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb + (q.n + 1) := by
      simp only [t2KMy, aqKm, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;> simp <;> omega
    rcases AxSpinApA.aqTailW Hit with ⟨hj, rfl, rfl⟩ | ⟨hb, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inl (by omega)⟩)))
    · exact Or.inl ⟨rfl, by omega, by omega⟩
  rw [List.length_map, aqTailLen] at h4 H
  rcases AxSpinApA.appCase H with ⟨h5, H⟩ | ⟨h5, H⟩
  · -- the critical-section body
    rw [List.length_map, AxSpinAp7.apBodyShLen] at h5
    rw [List.getElem?_map] at H
    obtain ⟨it, Hit, rfl⟩ := Option.map_eq_some_iff.1 H
    rw [AxSpinApA.itRS Hxw] at Hit
    have hk : t2KBd q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb + (q.n + 1) + 8 := by
      simp only [t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;> simp <;>
        omega
    rcases AxSpinApA.bodyW Hit with ⟨hj, rfl, rfl⟩ | ⟨hj, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, .inl rfl⟩))))
  rw [List.length_map, AxSpinAp7.apBodyShLen] at h5 H
  have hkr : t2KRl q = 3 + (17 + (if q.b then 5 else 0)) + holdLen q.hb + (q.n + 1) + 8 + 67 := by
    simp only [t2KRl, t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; cases q.b <;> cases q.hb <;>
      simp <;> omega
  rcases AxSpinApA.appCase H with ⟨h6, H⟩ | ⟨h6, H⟩
  · -- release
    unfold relSh at H
    rcases AxSpinApA.appCase H with ⟨h7, H⟩ | ⟨h7, H⟩
    · have := AxSpinApA.mapW H Hxw
      refine Or.inl ?_
      clear Hx H Hk Hs Hxw Hpre
      simp only [relHead, List.mem_cons, List.not_mem_nil, or_false, Ritem.RS.injEq] at this
      omega
    rw [List.length_map] at h7 H
    rcases AxSpinApA.appCase H with ⟨h8, H⟩ | ⟨h8, H⟩
    · have := AxSpinApA.mapW H Hxw
      refine Or.inl ?_
      clear Hx H Hk Hs Hxw Hpre
      simp only [holdShB, mycSh, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, Ritem.RS.injEq, false_or] at this
      omega
    rw [List.length_map, holdShBLen] at h8 H
    have hl : (relHead (S - 8) (S - 16) (S - 24)).length = 3 := rfl
    have hh : holdLen true = 12 := rfl
    rcases AxSpinApA.appCase H with ⟨h9, H⟩ | ⟨h9, H⟩
    · rcases AxSpinApA.get3 H with ⟨hj, rfl⟩ | ⟨hj, rfl⟩ | ⟨hj, rfl⟩ <;>
        simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at Hxw
      · obtain ⟨rfl, rfl⟩ := Hxw
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inr (by simp only [relKc]; omega)⟩)))
      · obtain ⟨rfl, rfl⟩ := Hxw
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, .inr (by simp only [relKw]; omega)⟩))
    have h3l : ([Rxitem.it (.RS (AxSpinT2a.zLk + 16) 8), .RB true true false true,
        .RSc AxSpinT2a.zLk 4 .WCrel] : List Rxitem).length = 3 := rfl
    rcases AxSpinApA.appCase H with ⟨h10, H⟩ | ⟨h10, H⟩
    · -- pop_off (the noff store by position)
      rw [List.getElem?_map] at H
      obtain ⟨it, Hit, rfl⟩ := Option.map_eq_some_iff.1 H
      rw [AxSpinApA.itRS Hxw] at Hit
      have hpp : t2KPp q = t2KRl q + 18 := rfl
      rcases AxSpinApB.ppShW Hit with ⟨rfl, rfl, hj⟩ | ⟨hs, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, .inl ⟨rfl, .inr (by omega)⟩⟩)
      · exact Or.inl ⟨rfl, by omega, by omega⟩
    · have := AxSpinApA.mapW H Hxw
      simp [relTail] at this
  · -- the terminal store
    have Hlt : k < t2Len q :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 Hk).1 Hpre.2.1
    rw [relShLen] at h6 H
    have hTl : t2Len q = t2KRl q + relLen q.c + 1 := by rw [t2Len, AxSpinT2a.kTEq]
    rw [show k - 3 - (17 + (if q.b then 5 else 0)) - holdLen q.hb - (q.n + 1) - 8 - 67 -
      relLen q.c = 0 by omega] at H
    simp only [List.getElem?_cons_zero, Option.some.injEq] at H
    subst H
    simp only [AxSpinApA.xWm, Option.some.injEq, Prod.mk.injEq] at Hxw
    obtain ⟨rfl, rfl⟩ := Hxw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, .inr rfl⟩))))

/-- `AxSpinApA.segWr` on prefixes (positions of the cpu-field stores forgotten). -/
theorem AxSpinApB.segWrA (k : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    row[k]? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    AxSpinApA.WrAt q i S p k b m :=
  fun h1 h2 => AxSpinApB.wrAtOfP (AxSpinApB.segWrP Hpre k lb rl b m h1 h2)

variable (Hlay : AxSpinApA.Lay i S p)
include Hlay

/-- Ap9's `Hone` on prefixes. -/
theorem AxSpinApB.npOnlyP (k' : Nat) (lb : Lbl) (rl : Bool) (m : Nat) :
    row[k']? = some lb → aidentWr (aident lb) = some (rl, AxSpinT2a.zNp, m) →
    k' = t2KBd q + 65 := by
  intro Hk Hw
  have N := AxSpinApA.nums Hlay
  rcases AxSpinApB.segWrA Hpre k' lb rl _ m Hk Hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
    ⟨-, -, h⟩ | ⟨-, h⟩
  all_goals first | exact h | omega

theorem AxSpinApB.npBeforeP (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    k' < t2KBd q → row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    dj b m AxSpinT2a.zNp 4 := by
  intro hk Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  unfold dj
  rcases AxSpinApB.segWrA Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem AxSpinApB.lkBetweenP (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    t2KA q < k' → k' < t2KRh q → row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    dj b m AxSpinT2a.zLk 1 := by
  intro hk1 hk2 Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  unfold dj
  rcases AxSpinApB.segWrA Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem AxSpinApB.clbBetweenP (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    t2KMy q + 4 < k' → k' < t2KRh q + 4 → row[k']? = some lb →
    aidentWr (aident lb) = some (rl, b, m) → dj b m (AxSpinT2a.zLk + 16) 8 := by
  intro hk1 hk2 Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  unfold dj
  rcases AxSpinApB.segWrA Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

/-- No row write before acquire's holding `lk->cpu` read touches `lk->cpu` (cutAq's `Hns`). -/
theorem AxSpinApB.clbBefore (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat) :
    k' < t2KHd q + 4 → row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) →
    dj b m (AxSpinT2a.zLk + 16) 8 := by
  intro hk Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  have K := AxSpinT2f.kEqs q
  unfold dj
  rcases AxSpinApB.segWrA Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem AxSpinApB.wle4P (b : Int)
    (hb : b = cpuZ i + 120 ∨ b = cpuZ i + 124 ∨ b = p + 48 ∨ b = p + 24) : rowWle row b 4 := by
  intro k' lb rl m Hk Hw
  have N := AxSpinApA.nums Hlay
  rcases AxSpinApB.segWrA Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, h⟩ <;> omega

/-- release's lock-word window (`allocRelWinC` on prefixes): after release's `sd zero,16(s1)`,
the only lock-word write is release's `sw zero,0(s1)`. -/
theorem AxSpinApB.relWinCP (L : Xlay) (hL : L.xlLk = AxSpinT2a.zLk) (k' : Nat) (lb : Lbl)
    (rl : Bool) (n : Nat) :
    relKc (t2KRl q) < k' → row[k']? = some lb → aidentWr (aident lb) = some (rl, L.xlLk, n) →
    k' = relKw (t2KRl q) := by
  intro hk Hk Hw
  rw [hL] at Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  rcases AxSpinApB.segWrA Hpre k' lb rl _ n Hk Hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ |
    ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩ <;> omega

/-- push_off's two noff loads read the boot image: no row write BEFORE them touches
`cpus[cpuOf i].noff` (the genesis premise `noWrBefore` of push_off's annotations). -/
theorem AxSpinApB.noffNoWrB (k0 : Nat) (hk0 : k0 ≤ t2KPoT q + 5) :
    AxSpinLd4P.noWrBefore row k0 (cpuZ i + 120) 4 := by
  intro k' lb rl b m hk Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  have K := AxSpinT2f.kEqs q
  unfold dj
  rcases AxSpinApB.segWrP Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ |
    ⟨rfl, (⟨rfl, h⟩ | ⟨rfl, -, h⟩)⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, h⟩ <;> omega

/-- No write to `noff` strictly between push_off's `sw noff` and pop_off's `lw noff` (pop_off's
noff reload premise). -/
theorem AxSpinApB.noffNowr :
    nowr row (t2KPoT q + 5) (t2KPp q + 6) (cpuZ i + 120) 4 := by
  intro k' lb rl b m hk Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  have K := AxSpinT2f.kEqs q
  unfold dj
  rcases AxSpinApB.segWrP Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ |
    ⟨rfl, (⟨rfl, h⟩ | ⟨rfl, -, h⟩)⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, h⟩ <;> omega

/-- No write to `intena` strictly between push_off's `sw intena` and pop_off's `lw intena`. -/
theorem AxSpinApB.intenaNowr :
    nowr row (t2KPo + 12) (t2KPp q + 8) (cpuZ i + 124) 4 := by
  intro k' lb rl b m hk Hk Hw
  have N := AxSpinApA.nums Hlay
  have P := AxSpinApB.posF q
  have K := AxSpinT2f.kEqs q
  unfold dj
  unfold t2KPo at hk
  rcases AxSpinApB.segWrP Hpre k' lb rl b m Hk Hw with ⟨rfl, h⟩ |
    ⟨rfl, (⟨rfl, h⟩ | ⟨rfl, -, h⟩)⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, h⟩ <;> (try unfold t2KPo at h) <;> omega

/-- hart `i`'s private ranges miss the lock word's base. -/
theorem AxSpinApB.privNeP : ∀ a, AxSpinT2a.privZ S p i a → a ≠ AxSpinT2a.zLk := by
  intro a ha
  have N := AxSpinApA.nums Hlay
  unfold AxSpinT2a.privZ at ha
  omega

end pre

/-! ## Reading positions off the prefix shape -/

theorem AxSpinApB.rdOfP {k : Nat} {row : List Lbl} {sh : List Ritem} {j : Nat} {pa : Int}
    {n : Nat} (H : RowShP k row sh) (hj : sh[j]? = some (.RL pa n)) (hk : k + j < row.length) :
    AxSpinT2h.RdAt row (k + j) pa n := by
  obtain ⟨lb, Hlb, aq, Hs⟩ := H j _ hj hk
  exact ⟨lb, Hlb, aq, Hs⟩

theorem AxSpinApB.rdOfXP {k : Nat} {row : List Lbl} {sh : List Rxitem} {j : Nat} {pa : Int}
    {n : Nat} (H : RowShXP k row sh) (hj : sh[j]? = some (.it (.RL pa n)))
    (hk : k + j < row.length) : AxSpinT2h.RdAt row (k + j) pa n := by
  obtain ⟨lb, Hlb, aq, Hs⟩ := H j _ hj hk
  exact ⟨lb, Hlb, aq, Hs⟩

/-- A read item has a graph value. -/
theorem AxSpinApB.gvOfRd (GD : Gdexec) (i k : Nat) (pa : Int) (n : Nat) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k pa n → ∃ vs, graphValue GD (i, k) = some vs := by
  rintro ⟨lb, Hlb, aq, Hid⟩
  obtain ⟨vs, hv⟩ := AxSpinT2f.rdVal Hid
  refine ⟨vs, ?_⟩
  rw [AxSpinT2f.gvGrow]
  simp only [AxSpinT2f.rv, Hlb, Option.bind_some, hv]

/-- An 8-byte load's value is its own `stBytes`. -/
theorem AxSpinApB.st8 (vs : List (BitVec 8)) (h : vs.length = 8) :
    stBytes 8 (ldRes false 8 vs) = vs := by
  rw [AxSpinRl2.stBytes8, AxSpinT2g.ldRes8Eq vs h, wbytesWordOfBytes 8 vs h]


/-- `gvOfRd` with the width. -/
theorem AxSpinApB.gvRd (GD : Gdexec) (i k : Nat) (pa : Int) (n : Nat) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k pa n →
    ∃ vs, graphValue GD (i, k) = some vs ∧ vs.length = n := by
  intro Hr
  obtain ⟨vs, hv⟩ := AxSpinApB.gvOfRd GD i k pa n Hr
  obtain ⟨-, -, -, hl⟩ := AxSpinT2h.ldOfRd GD i k pa n vs Hr hv
  exact ⟨vs, hv, hl⟩

theorem AxSpinApB.rdCongr {row : List Lbl} {k k' : Nat} {pa : Int} {n : Nat}
    (h : AxSpinT2h.RdAt row k pa n) (e : k = k') : AxSpinT2h.RdAt row k' pa n := e ▸ h

/-- holding's prefix window for either branch (`AxSpinRl4.rowHoldingPOf` needs the long one). -/
theorem AxSpinApB.holdP (k : Nat) (row : List Lbl) (hb : Bool)
    (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowShP k row (holdShB hb plk pcl pra ps0 ps1 pram ps0m) →
    (k < row.length → lkBranch row k hb) →
    RowHoldingP k row hb plk pcl pra ps0 ps1 pram ps0m := by
  intro H Hb
  cases hb with
  | true => exact AxSpinRl4.rowHoldingPOf k row true _ _ _ _ _ _ _ H Hb
  | false =>
    refine ⟨Hb, fun j Hj Hk => ?_⟩
    match j, Hj, Hk with
    | 0, _, Hk => exact H 0 _ rfl Hk

/-- acquire's prefix row (`allocAcquire` on prefixes). -/
theorem AxSpinApB.acqP {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
    (Hpre : allocPre row q i S p) :
    RowAcquireP 0 q.b q.hb q.n row (S - 8) (S - 16) (S - 24) (S - 40) (S - 48) (S - 56) (S - 72)
      (S - 80) (cpuZ i + 120) (cpuZ i + 124) (S - 40) (S - 48) (S - 56) (S - 72) (S - 80)
      AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) := by
  obtain ⟨H0, H1, H2, H3, H4, -, -, -⟩ := AxSpinT2f.segPartsP Hpre.1
  refine ⟨H0, H1, AxSpinApB.holdP _ _ _ _ _ _ _ _ _ _ H2 Hpre.2.2.1, fun j hj hk => ?_, H4⟩
  obtain ⟨lb, Hlb, Hs⟩ := H3 j _ (List.getElem?_replicate_of_lt (by omega)) hk
  exact ⟨lb, Hlb, Hs⟩

/-- the `rlS` gate from holding's lock bit `true` (vacuous when the read is absent). -/
theorem AxSpinApB.gateRlSOf {row : List Lbl} {q : T2Prm} {i : Agent}
    (h : t2KRh q < row.length → lkBranch row (t2KRh q) true) : t2GateOk .rlS row q i := by
  intro vs hv
  have hlt : t2KRh q < row.length := by
    unfold AxSpinT2f.rv at hv
    cases hk : row[t2KRh q]? with
    | none => simp [hk] at hv
    | some lb => exact (List.getElem?_eq_some_iff.1 hk).1
  obtain ⟨lb, vs', h1, h2, h3⟩ := h hlt
  simp only [AxSpinT2f.rv, h1, Option.bind_some, h2, Option.some.injEq] at hv
  subst hv
  intro h0
  rw [h0] at h3
  simp at h3

/-- A row ending at `k` is no cut row when every designated cut at `k` took the normal arm. -/
theorem AxSpinApB.notCutAt {row : List Lbl} {q : T2Prm} {i : Agent} (k : Nat)
    (hk : row.length = k) (haq : q.hb = true → k ≠ t2KHd q + 12)
    (hrs : k = t2KRh q + 1 → t2GateOk .rlS row q i) (hrl : k ≠ t2KRh q + 12)
    (hpn : k ≠ t2KPp q + 7) (hpi : q.c = false → k ≠ t2KPp q + 9) :
    ¬ t2CutAt row q i := by
  apply notCutAtOfGates
  intro j hj
  rw [hk] at hj
  cases j with
  | aq => intro hb; exact absurd hj (haq hb)
  | rlS => exact hrs hj
  | rlL => exact absurd hj hrl
  | ppN => exact absurd hj hpn
  | ppI => intro hc; exact absurd hj (hpi hc)

/-! # 2. The hypothesis bundle on prefix rows -/

/-- THE HYPOTHESES of the PREFIX segment WPd (`AxSpinApA.Hyp` with `allocPre`, the guarded pins
`AllocPins2` and the noff image premise `HimgNoff`'s instance for `i`). -/
structure AxSpinApB.Hyp2 (L : Xlay) (GT : GdexecT) (σi : ExecSt) (T : PTree) (i : Agent)
    (q : T2Prm) (S p : Int) : Prop where
  pre : allocPre (AxOpsem.grow (gtAdGd GT) i) q i S p
  pins : AllocPins2 (gtAdGd GT) i q
  imgN : ∃ v, noffImgOk (gtAdGd GT).gdG.gxImg i v
  lay : AxSpinApA.Lay i S p
  hLk : L.xlLk = AxSpinT2a.zLk
  hNp : L.xlNp = AxSpinT2a.zNp
  hpriv : ∀ a, AxSpinT2a.privZ S p i a → priv L a i
  ntx : ∀ a, ¬ AxSpinT2a.textZ a → ¬ L.xlText a
  map : AxSpinApA.MapOk σi T i S p
  txa : acquireText σi T
  txm : mycpuText σi T
  txp : pushOffText σi T
  txh : holdingText σi T
  txq : popOffText σi T
  txr : releaseText σi T
  txc : allocpidText σi T
  txt : AxSpinApA.tailText σi T
  fix : textFixed (gtAdGd GT) i (imgS σi)

section bundles
variable {L : Xlay} {GT : GdexecT} {σi : ExecSt} {T : PTree} {i : Agent} {q : T2Prm} {S p : Int}
variable (H : AxSpinApB.Hyp2 L GT σi T i q S p)
include H

theorem AxSpinApB.ntxOf (a : Int) (h : 0x80007000 ≤ a) : ¬ L.xlText a := by
  refine H.ntx a ?_
  unfold AxSpinT2a.textZ
  obtain ⟨-, -, -, -, -, -, v7, v8⟩ := AxSpinT2a.symV
  rw [v8]
  omega

theorem AxSpinApB.dat (acc : MemoryAccessType mem_payload)
    (hacc : acc = .Load .Data ∨ acc = .Store .Data ∨ acc = accAmo true) (a : Int) (w : Nat)
    (hw : w = 4 ∨ w = 8) (hal : a % (w : Int) = 0) (hr : AxSpinApA.Rng i S p a w) :
    dataAtS σi T acc (BitVec.ofInt 64 a) w (BitVec.ofInt 64 a) :=
  H.map acc a w hacc hw hal hr

theorem AxSpinApB.hitStk (rs : RegFile) (hw : AxSpinApA.Warm rs i S p) (a : Int)
    (h1 : S - 80 ≤ a) (h2 : a < S) : hitW rs (BitVec.ofInt 64 a) := by
  have N := AxSpinApA.nums H.lay
  refine hw _ (t2TouchStk i S p _ ?_ ?_) <;> rw [AxSpinApA.toNatOf a (by omega) (by omega)] <;>
    omega

theorem AxSpinApB.slot (rs : RegFile) (hw : AxSpinApA.Warm rs i S p) (d : Int) (h1 : 8 ≤ d)
    (h2 : d ≤ 80) (h3 : d % 8 = 0) :
    AxSpinPO1.slot8 σi T L i rs (BitVec.ofInt 64 (S - d)) (BitVec.ofInt 64 (S - d)) := by
  have N := AxSpinApA.nums H.lay
  have hz := AxSpinApA.paZOf (S - d) (by omega) (by omega)
  refine ⟨AxSpinApB.dat H _ (.inr (.inl rfl)) _ 8 (.inr rfl) (by omega) (.inl ⟨by omega, by omega⟩),
    AxSpinApB.dat H _ (.inl rfl) _ 8 (.inr rfl) (by omega) (.inl ⟨by omega, by omega⟩),
    AxSpinApB.hitStk H rs hw _ (by omega) (by omega), ?_, ?_⟩
  · intro j hj
    rw [hz]
    exact H.hpriv _ (.inl ⟨by omega, by omega⟩)
  · rw [hz]
    exact AxSpinApB.ntxOf H _ (by omega)

theorem AxSpinApB.fld (rs : RegFile) (hw : AxSpinApA.Warm rs i S p) (c : Int)
    (hc : c = 120 ∨ c = 124) :
    fld4 σi T L i rs (BitVec.ofInt 64 (cpuZ i + c)) (BitVec.ofInt 64 (cpuZ i + c)) := by
  have N := AxSpinApA.nums H.lay
  have hz := AxSpinApA.paZOf (cpuZ i + c) (by omega) (by omega)
  refine ⟨AxSpinApB.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega)
      (.inr (.inl ⟨by omega, by omega⟩)),
    AxSpinApB.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega) (.inr (.inl ⟨by omega, by omega⟩)),
    hw _ ?_, ?_, ?_⟩
  · refine .inr (.inr (.inr (.inl ?_)))
    rw [AxSpinApA.toNatOf _ (by omega) (by omega)]
    omega
  · intro j hj
    rw [hz]
    exact H.hpriv _ (.inr (.inr (.inr ⟨by omega, by omega⟩)))
  · rw [hz]
    exact AxSpinApB.ntxOf H _ (by omega)

end bundles

/-- AxSpinRl2's `CpuWin` from the PREFIX family (`allocCpuWin` on `allocPre`). -/
theorem AxSpinApB.cpuWinP (L : Xlay) (GT : GdexecT) (i : Agent) (q : T2Prm) (S p : Int)
    (e : Geid) (Hpre : allocPre (AxOpsem.grow (gtAdGd GT) i) q i S p)
    (hL : L.xlLk = AxSpinT2a.zLk)
    (Hlob : ∀ (k : Nat) (lb : Lbl) (rl : Bool) (m : Nat), e.2 < k →
      (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk + 16, m) →
      e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k)) :
    CpuWin L GT i e := by
  intro k lb rl m hk Hlb Hid
  refine ⟨?_, Hlob k lb rl m hk Hlb Hid⟩
  rw [hL] at Hid ⊢
  exact Hpre.2.2.2.2.2.2.1 k lb rl m Hlb Hid

/-! # 3. THE POST on prefix rows, and the row ends -/

/-- THE STAGE-2 POST (one hart, parameters `q`): at a non-mid state, the row is NOT a cut row
(no designated gate took its off arm), and IF the row is complete (`LEN = t2Len q`) the stage-1
post `AxSpinApA.t2PostS` holds (an issued pid `w`, the `p->pid` store's data, `npSrc`, the
exclusive fragment). -/
def AxSpinApB.t2PostP {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (GD : Gdexec) (L : Xlay)
    (nm : Xv6N) (i : Agent) (q : T2Prm) (s : Athread) : IProp GF :=
  iprop(⌜¬ midState s⌝ -∗ ⌜¬ t2CutAt (AxOpsem.grow GD i) q i⌝ ∗
    (⌜(AxOpsem.grow GD i).length = t2Len q⌝ -∗ ∃ w : BitVec 32,
      ⌜pidOf GD i q = some (WeakInterpProj.wbytes 4 w) ∧
        npSrc GD.gdG L (i, t2KBd q) (i, t2KA q)⌝ ∗ FRAG nm w))

/-- The post at an INCOMPLETE row end that is no cut row is free. -/
theorem AxSpinApB.postP {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (GD : Gdexec) (L : Xlay)
    (nm : Xv6N) (i : Agent) (q : T2Prm) (hc : ¬ t2CutAt (AxOpsem.grow GD i) q i)
    (hl : (AxOpsem.grow GD i).length < t2Len q) (s : Athread) :
    ⊢ AxSpinApB.t2PostP (GF := GF) GD L nm i q s := by
  unfold AxSpinApB.t2PostP
  iintro %_
  isplitr
  · ipureintro
    exact hc
  · iintro %h
    exact absurd h (by omega)

/-- The post at a DESIGNATED CUT whose gate took the normal arm is free. -/
theorem AxSpinApB.postCut {GF : BundledGFunctors} [AxSpinX.Xv6G GF] (GD : Gdexec) (L : Xlay)
    (nm : Xv6N) (i : Agent) (q : T2Prm) (j : T2Cj)
    (hL : (AxOpsem.grow GD i).length = cutPos j q) (hG : t2GateOk j (AxOpsem.grow GD i) q i)
    (s : Athread) : ⊢ AxSpinApB.t2PostP (GF := GF) GD L nm i q s := by
  refine AxSpinApB.postP GD L nm i q ?_ (by rw [hL]; exact AxSpinT2f.cutPosLen j q) s
  apply notCutAtOfGates
  intro j' hj'
  have e := AxSpinT2f.cutPosInj (hL.symm.trans hj')
  subst e
  exact hG

section rowend
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- The mid-instruction states' post is free (the `¬ midState` guard). -/
theorem AxSpinApB.postSMidP (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (q : T2Prm) :
    ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) (AxSpinApB.t2PostP (gtAdGd GT) L nm i q) i s := by
  intro s Hm _
  refine @postLiftingTrue GF (AxSpinX2.xG L GT nm) _ _ i s ?_
  unfold AxSpinApB.t2PostP
  iintro - %Hn
  exact absurd Hm Hn

/-- PAST (OR AT) THE ROW END, a PURE post: from `k0 ≥ LEN` every program state's WPd holds when
the post holds at `k0 = LEN`; at `k0 > LEN` the row-end clause is never reached (admin steps keep
the position), so the post is not demanded there. -/
theorem AxSpinApB.wpdPast (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (Φ : Athread → IProp GF)
    (HRQ : k0 = (AxOpsem.grow (gtAdGd GT) i).length → ∀ s, ⊢ Φ s) (pr : Pexv6) :
    ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have Hnone : (AxOpsem.grow (gtAdGd GT) i)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ pr : Pexv6,
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
    iloeb as IH
    iintro %pr
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT)
      rvwmoCatConsistent .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (AxSpinX2.xG L GT nm) _ i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := (AxSpinWit.gconstEq (gtAdGd GT) Xv6N Unit (protXv6 L) nm GD') $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk'⟩ := AxSpinApA.rowEndShape _ _ l s' Hnone Hst
      rw [AxSpinRow.lbAdminWdata l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p'
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p'
    · iintro %Hk
      simp only at Hk
      iapply (@postLiftingTrue GF (AxSpinX2.xG L GT nm) _ _ i _ (by
        iintro -
        iapply (HRQ Hk _)))
  iapply H $$ %pr

/-- THE RESOURCE-FREE HOOK for `t2PostP` (Q-S2-2): at a row position `k' < t2Len q` with
`LEN ≤ k'`, unless `k'` is a designated cut whose gate may be flipped. -/
theorem AxSpinApB.hookP (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (q : T2Prm)
    (k' : Nat) (hlt : k' < t2Len q) (haq : q.hb = true → k' ≠ t2KHd q + 12)
    (hrs : k' = t2KRh q + 1 → t2GateOk .rlS (AxOpsem.grow (gtAdGd GT) i) q i)
    (hrl : k' ≠ t2KRh q + 12) (hpn : k' ≠ t2KPp q + 7) (hpi : q.c = false → k' ≠ t2KPp q + 9)
    (hL : (AxOpsem.grow (gtAdGd GT) i).length ≤ k') (pr : Pexv6) :
    ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k'⟩ (AxSpinApB.t2PostP (gtAdGd GT) L nm i q) :=
  AxSpinApB.wpdPast L GT nm i k' hL _ (fun hk s => AxSpinApB.postP (gtAdGd GT) L nm i q
    (AxSpinApB.notCutAt k' hk.symm haq hrs hrl hpn hpi) (by omega) s) pr

end rowend


/-! # 4. The pieces of the segment on prefix rows -/

section seg
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_apb_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-- (Lean-only) `paZ (ofInt a) = a` everywhere, side conditions by `omega`. -/
local macro "ax_spin_apb_pz" : tactic =>
  `(tactic| simp (disch := omega) only [AxSpinApA.paZOf])

/-- (Lean-only) pairwise disjointness of concrete ranges. -/
local macro "ax_spin_apb_dj" : tactic =>
  `(tactic| (simp [List.pairwise_cons, dj, disj8] <;> omega))

set_option maxHeartbeats 6400000 in
include HL Hcons hmode hasid hppn in
/-- THE RELEASE PIECE on a PREFIX row: from `jal release` (allocproc + 0x94, row position
`t2KRl q`) through release (`wpdReleaseP`, holding's lock bit `hbR` read off the row; the four
designated cuts of release's row are AxSpinT2h's arms: `cutRelS`, `cutRelL`, and `cutPpNF` /
`cutPpIF` with push_off's genesis annotations as the FRAME), `c.li a5,1` and the terminal
private store to the row end `t2Len q`.  Every row end before is the hook `AxSpinApB.hookP`. -/
theorem AxSpinApB.segRelP (q : T2Prm) (S p : Int) (H : AxSpinApB.Hyp2 L GT σi T i q S p)
    (rsR : RegFile) (ibR : Ibch) (cls clsN clsI : WmClass) (vp : List (BitVec 8)) :
    ctrlOkSW T satp0 rsR → rsR .PC = pca 0x94 → AxSpinApA.Warm rsR i S p →
    gprVal rsR 2#5 = BitVec.ofInt 64 S → gprVal rsR 4#5 = hartId (cpuOf i) →
    gprVal rsR 9#5 = BitVec.ofInt 64 p →
    gprVal rsR 10#5 = BitVec.ofNat 64 KernelSyms.«pid_lock» →
    (AxOpsem.grow (gtAdGd GT) i)[t2KMy q + 4]? = some (.LStore false (L.xlLk + 16)
      (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i)))) cls) →
    (AxOpsem.grow (gtAdGd GT) i)[t2KPoT q + 5]? = some (.LStore false
      (paZ (BitVec.ofInt 64 (cpuZ i + 120))) (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vp)))
      clsN) →
    (q.b = true → (AxOpsem.grow (gtAdGd GT) i)[t2KPo + 12]? = some (.LStore false
      (paZ (BitVec.ofInt 64 (cpuZ i + 124))) (stBytes 4 0#64) clsI)) →
    graphValue (gtAdGd GT) (i, t2KPoT q + 4) = some vp →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, t2KA q) (locked nm.xnReg L.xlLk i (i, t2KA q)) -∗
      AxAnnot.annotOwn (GF := GF) (i, t2KMy q + 4)
        iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, t2KMy q + 4)
          (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i))))) -∗
      AxAnnot.annotOwn (i, t2KBd q + 65)
        (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, t2KBd q + 65)) -∗
      AxSpinT2h.genF (GF := GF) GT i (paZ (BitVec.ofInt 64 (cpuZ i + 120))) (t2KPo + 7)
        (t2KPoT q + 4) -∗
      (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x9c ∧ rs' .tlb = rsR .tlb ∧
          gprVal rs' 13#5 = gprVal rsR 13#5 ∧ (AxOpsem.grow (gtAdGd GT) i).length = t2Len q⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', t2Len q⟩ (AxSpinApB.t2PostP (gtAdGd GT) L nm i q)) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsR none ibR, t2KRl q⟩ (AxSpinApB.t2PostP (gtAdGd GT) L nm i q) := by
  intro Hc HPC Hw E2 E4 E9 E10 Hkw HlN HlI HgvN
  have Hpre := H.pre
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := AxSpinApA.nums H.lay
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, P10⟩ := AxSpinApB.posF q
  obtain ⟨K1, K2, K3, K4, K5, K6, K7, K8, K9⟩ := AxSpinT2f.kEqs q
  have hproc : (KernelSyms.«proc» : Int) = 0x80012930 := rfl
  have hle : (AxOpsem.grow (gtAdGd GT) i).length ≤ t2Len q := Hpre.2.1
  have hKe : relKe (t2KRl q) q.c = t2KRl q + 21 + ppLen q.c := by
    simp only [relKe, relKr, relKp]; omega
  have hKe1 : relKe (t2KRl q) q.c + 1 = t2Len q := rfl
  have hpn : paZ (BitVec.ofInt 64 (cpuZ i + 120)) = cpuZ i + 120 :=
    AxSpinApA.paZOf _ (by omega) (by omega)
  have hpi : paZ (BitVec.ofInt 64 (cpuZ i + 124)) = cpuZ i + 124 :=
    AxSpinApA.paZOf _ (by omega) (by omega)
  have HG := Hpre.2.2.2.2.2.2.2.2
  obtain ⟨-, Ppo, -, -, -, Pbd, Prl, -⟩ := AxSpinT2f.segPartsP Hpre.1
  obtain ⟨v, Himg⟩ := H.imgN
  have HΦmid := AxSpinApB.postSMidP (GF := GF) L GT nm i q
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix _ HΦmid
  have XS := XxStF L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix _ HΦmid
  have HP := H.pins
  iintro #Hil HLK HW HNp HGF K
  -- row end at t2KRl
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t2KRl q
  · iclear HLK HW HNp HGF K
    iapply (AxSpinApB.hookP L GT nm i q (t2KRl q) (by omega) (fun _ => by omega)
      (fun h => absurd h (by omega)) (by omega) (by omega) (fun _ => by omega) E0 _)
  -- the claim's label (present: t2KA < t2KRl < LEN)
  obtain ⟨tA, rvsA, HrmA, -⟩ := Hpre.2.2.2.2.2.1 q.n (Nat.le_refl _) (by omega)
  have HrmA' : (AxOpsem.grow (gtAdGd GT) i)[t2KA q]? =
      some (Lbl.LRmw true false L.xlLk [tA, tA, tA, tA] rvsA AxSpinX4.o4 .WCexcl) := by
    rw [H.hLk]; exact HrmA
  iapply (AxSpinApA.annotEntailX L GT nm i _ _ (i, t2KA q) _ _ (AxSpinApA.sepTrue _)) $$ HLK
  iintro HLK
  -- ---- + 0x94: jal ra,release (t2KRl) ----
  have Hcj : CertC (ctrlOkSW T satp0) rsR (pca 0x94) false ap94 (some (AxSpinHdB.prl 0))
      (some (1#5, BitVec.addInt (pca 0x94) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rsR (pca 0x94)
      false 2093274#21 1#5 (by decide)
    rw [show pca 0x94 + sign_extend (m := 64) 2093274#21 = AxSpinHdB.prl 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (pca 0x94) (incr false)) =
      some (1#5, BitVec.addInt (pca 0x94) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rsR (t2KRl q) (pca 0x94) false ap94 (some (AxSpinHdB.prl 0))
    (some (1#5, BitVec.addInt (pca 0x94) (incr false)))
    (retxRefl cpu rsR (t2KRl q) ibR) Hc HPC (AxSpinApA.hitTxt rsR Hw _ (by decide) (by decide))
    (atok94 σi T satp0 H.txc) (AxSpinE8.owOkSome 1#5 _ (by decide)) rfFAp94 Hcj (by omega))
  iintro %rsJ %ibJ %HGJ
  have HFJ := stepRegs T satp0 _ rsR _ _ _ _ _ rsJ (fun _ => rfl) HGJ
  have HPCJ : rsJ .PC = AxSpinHdB.prl 0 := by rw [gbPc T satp0 _ _ _ _ _ _ HGJ]; rfl
  have HtlJ : rsJ .tlb = rsR .tlb := gbTlb T satp0 _ _ _ _ _ _ HGJ
  have HcJ := gbCtrl T satp0 _ _ _ _ _ _ HGJ
  have HwJ := AxSpinApA.warmTlb rsR rsJ i S p HtlJ Hw
  have EJ2 : gprVal rsJ AxSpinE8.r2 = BitVec.ofInt 64 S := by
    rw [HFJ]; ax_spin_apb_zsimp; exact E2
  have EJ4 : gprVal rsJ AxSpinE8.r4 = hartId (cpuOf i) := by
    rw [HFJ]; ax_spin_apb_zsimp; exact E4
  have EJ9 : gprVal rsJ AxSpinHd8.r9 = BitVec.ofInt 64 p := by
    rw [HFJ]; ax_spin_apb_zsimp; exact E9
  have EJ10 : gprVal rsJ AxSpinE8.r10 = BitVec.ofNat 64 KernelSyms.«pid_lock» := by
    rw [HFJ]; ax_spin_apb_zsimp; exact E10
  have EJ13 : gprVal rsJ 13#5 = gprVal rsR 13#5 := by
    rw [HFJ]; ax_spin_apb_zsimp
  -- the nextpid store's label (present: t2KBd + 65 < t2KRl < LEN)
  obtain ⟨lbS, HlbS, vwS, clsS, HlS, -⟩ := Pbd 65 (.RS AxSpinT2a.zNp 4) rfl (by omega)
  -- push_off's arm read (vn0) and its second noff read (vp), and pop_off's / holding's reads
  have Rd1 : AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (t2KPo + 7) (cpuZ i + 120) 4 :=
    AxSpinApB.rdOfP Ppo (j := 7) (by cases q.b <;> rfl) (by unfold t2KPo; omega)
  obtain ⟨vn0, Hgv1⟩ := AxSpinApB.gvOfRd _ i _ _ _ Rd1
  have RdN2 : AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (t2KPoT q + 4) (cpuZ i + 120) 4 :=
    AxSpinApB.rdCongr (AxSpinApB.rdOfP Ppo (j := 8 + (if q.b then 5 else 0) + 4)
      (by cases q.b <;> rfl) (by unfold t2KPo; unfold t2KPoT t2KPo at P9; omega))
      (by unfold t2KPoT t2KPo; omega)
  have Rd6 : t2KPp q + 6 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (t2KPp q + 6) (cpuZ i + 120) 4 := fun h =>
    AxSpinApB.rdCongr (AxSpinApB.rdOfXP Prl (j := 24) (by cases q.c <;> rfl) (by omega))
      (by omega)
  have Rd8 : q.c = false → t2KPp q + 8 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (t2KPp q + 8) (cpuZ i + 124) 4 := fun hc h =>
    AxSpinApB.rdCongr (AxSpinApB.rdOfXP Prl (j := 26) (by rw [hc]; rfl) (by omega)) (by omega)
  have RdS : t2KRh q < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (t2KRh q) AxSpinT2a.zLk 4 := fun h =>
    AxSpinApB.rdCongr (AxSpinApB.rdOfXP Prl (j := 3) (by cases q.c <;> rfl) (by omega))
      (by omega)
  have RdL : t2KRh q + 4 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (t2KRh q + 4) (AxSpinT2a.zLk + 16) 8 :=
    fun h => AxSpinApB.rdCongr (AxSpinApB.rdOfXP Prl (j := 7) rfl (by omega)) (by omega)
  -- holding's lock bit on release's call, read off the row (`false` only at the `rlS` cut)
  obtain ⟨hbR, HbR1, HbR2⟩ : ∃ hb : Bool,
      (t2KRh q < (AxOpsem.grow (gtAdGd GT) i).length →
        lkBranch (AxOpsem.grow (gtAdGd GT) i) (t2KRh q) hb) ∧
      (hb = false → (AxOpsem.grow (gtAdGd GT) i).length ≤ t2KRh q + 1) := by
    by_cases hk : t2KRh q < (AxOpsem.grow (gtAdGd GT) i).length
    · obtain ⟨lb, h1, aq, h2⟩ := Prl 3 (.it (.RL AxSpinT2a.zLk 4)) (by cases q.c <;> rfl)
        (by omega)
      obtain ⟨vs, hv⟩ := AxSpinT2f.rdVal h2
      refine ⟨(ldRes false 4 vs != 0#64), fun _ => ⟨lb, vs, h1, hv, rfl⟩, ?_⟩
      intro hf
      apply Nat.le_of_not_lt
      intro hlt
      have G := HG .rlS (by simp only [cutPos]; omega) vs
        (by simp only [AxSpinT2f.rv, t2KRh, relKh, h1, Option.bind_some, hv])
      simp [G] at hf
    · exact ⟨true, fun h => absurd h hk, fun h => nomatch h⟩
  -- ---- release (P-form), at t2KRl ----
  iapply (wpdReleaseP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix H.txm H.txh H.txq
    H.txr _ HΦmid (t2KRl q) q.c hbR rsJ ibJ (pca 0x98)
    (BitVec.ofInt 64 (S - 8)) (BitVec.ofInt 64 (S - 16)) (BitVec.ofInt 64 (S - 24))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
    (BitVec.ofInt 64 (AxSpinT2a.zLk + 16)) (BitVec.ofInt 64 (AxSpinT2a.zLk + 16))
    (BitVec.ofInt 64 AxSpinT2a.zLk) (BitVec.ofInt 64 AxSpinT2a.zLk)
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 64))
    (BitVec.ofInt 64 (cpuZ i + 120)) (BitVec.ofInt 64 (cpuZ i + 124))
    AxSpinT2a.zLk (t2KA q) (t2KMy q + 4) (t2KBd q + 65)
    (AxSpinE8.mycpuRet (hartId (cpuOf i))) cls iprop(True) iprop(True)
    [tA, tA, tA, tA] rvsA AxSpinX4.o4 .WCexcl
    (some (t2KPoT q + 5, stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vp)), clsN))
    (if q.b then some (t2KPo + 12, stBytes 4 0#64, clsI) else none)
    (AxSpinT2h.genF GT i (paZ (BitVec.ofInt 64 (cpuZ i + 120))) (t2KPo + 7) (t2KPoT q + 4))
    (by ax_spin_apb_pz; exact ⟨Prl, HbR1, HbR2⟩) (AxSpinApB.w8P Hpre)
    (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _)
    (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _)
    (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _)
    (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _) (AxSpinApB.noRmw8P Hpre _)
    (AxSpinApB.noRmw8P Hpre _)
    (by ax_spin_apb_pz; exact AxSpinApB.wle4P Hpre H.lay _ (.inl rfl))
    (AxSpinApB.noRmwnP Hpre _ 4 (.inl (by ax_spin_apb_pz; omega)))
    (AxSpinApB.noRmwnP Hpre _ 4 (.inl (by ax_spin_apb_pz; omega)))
    HcJ HPCJ (AxSpinApA.hitTxt rsJ HwJ _ (by decide) (by decide))
    (AxSpinApA.hitTxt rsJ HwJ _ (by decide) (by decide))
    (by rw [EJ2, AxSpinApA.aA24]; exact AxSpinApB.slot H rsJ HwJ 8 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aA16]; exact AxSpinApB.slot H rsJ HwJ 16 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aA8]; exact AxSpinApB.slot H rsJ HwJ 24 (by omega) (by omega) (by omega))
    (by ax_spin_apb_pz; apply AxSpinApA.alldjOf; ax_spin_apb_dj)
    (by ax_spin_apb_pz; simp only [relWr]; ax_spin_apb_dj)
    (by rw [EJ2, AxSpinApA.aH24]; exact AxSpinApB.slot H rsJ HwJ 40 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aH16]; exact AxSpinApB.slot H rsJ HwJ 48 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aH8]; exact AxSpinApB.slot H rsJ HwJ 56 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aQm8]; exact AxSpinApB.slot H rsJ HwJ 72 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aQm0]; exact AxSpinApB.slot H rsJ HwJ 80 (by omega) (by omega) (by omega))
    (by ax_spin_apb_pz; apply AxSpinApA.slotsDisjOf; ax_spin_apb_dj)
    (by rw [EJ2, AxSpinApA.aM8]; exact AxSpinApB.slot H rsJ HwJ 40 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aM0]; exact AxSpinApB.slot H rsJ HwJ 48 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aMm8]; exact AxSpinApB.slot H rsJ HwJ 56 (by omega) (by omega) (by omega))
    (by rw [EJ2, AxSpinApA.aMm0]; exact AxSpinApB.slot H rsJ HwJ 64 (by omega) (by omega) (by omega))
    (by rw [EJ4, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i120Of rfl]
        exact AxSpinApB.fld H rsJ HwJ 120 (.inl rfl))
    (by rw [EJ4, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i124Of rfl]
        exact AxSpinApB.fld H rsJ HwJ 124 (.inr rfl))
    (by ax_spin_apb_pz; apply AxSpinApA.alldjOf; ax_spin_apb_dj)
    (by rw [EJ10, AxSpinApA.lk0, show AxSpinT2a.zLk = AxSpinT2a.zLk + 0 by omega]
        exact AxSpinApA.hitLk rsJ HwJ 0 (by omega) (by omega))
    (by rw [EJ10, AxSpinApA.lk16]; exact AxSpinApA.hitLk rsJ HwJ 16 (by omega) (by omega))
    (by rw [EJ10, AxSpinApA.lk0]
        exact AxSpinApB.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by ax_spin_apb_pz; exact AxSpinApB.ntxOf H _ (by omega))
    (by rw [EJ10, AxSpinApA.lk0]
        exact AxSpinApB.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [H.hLk]; ax_spin_apb_pz)
    (by rw [EJ10, AxSpinApA.lk16]
        exact AxSpinApB.dat H _ (.inl rfl) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [H.hLk]; ax_spin_apb_pz)
    (by ax_spin_apb_pz; exact AxSpinApB.ntxOf H _ (by omega))
    (by rw [EJ10, AxSpinApA.lk16]
        exact AxSpinApB.dat H _ (.inr (.inl rfl)) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [H.hLk]; ax_spin_apb_pz)
    (fun _ => HrmA') (by simp only [relKh]; omega)
    (by
      intro w v Hwb Hpo1 Hpo2
      obtain ⟨lb, rl, b, m, t, Hlb, Hid, Ht, Ha⟩ := AxSpinApA.gwbRow _ w _ _ Hwb
      obtain ⟨hw1, hw2, -, -⟩ := Hpo1
      obtain ⟨-, hw3, -, -⟩ := Hpo2
      simp only at hw1 hw2 hw3
      rw [← hw1] at Hlb
      have := AxSpinApB.lkBetweenP Hpre H.lay w.2 lb rl b m hw2 hw3 Hlb Hid
      rw [H.hLk] at Ha
      unfold dj at this
      omega)
    (fun _ => Hkw) (by simp only [relKh]; omega)
    (by
      intro w a v Ha Hwb Hpo1 Hpo2
      obtain ⟨lb, rl, b, m, t, Hlb, Hid, Ht, Hab⟩ := AxSpinApA.gwbRow _ w _ _ Hwb
      obtain ⟨hw1, hw2, -, -⟩ := Hpo1
      obtain ⟨-, hw3, -, -⟩ := Hpo2
      simp only at hw1 hw2 hw3
      rw [← hw1] at Hlb
      have := AxSpinApB.clbBetweenP Hpre H.lay w.2 lb rl b m hw2 hw3 Hlb Hid
      unfold clb at Ha
      rw [inClr, H.hLk] at Ha
      unfold dj at this
      omega)
    (AxSpinApB.cpuWinP L GT i q S p _ Hpre H.hLk (by
      intro k lb rl m hk Hlb Hid
      obtain ⟨vw, cls', rfl, Hv⟩ := Hpre.2.2.2.2.2.2.1 k lb rl m Hlb (by rw [← H.hLk]; exact Hid)
      refine AxSpinRl2.lobpCpuSt GT Hcons (L.xlLk + 16) i _ k _ vw cls cls' Hkw
        (List.ne_nil_of_length_pos (by rw [wbytesLength]; omega)) (by rw [H.hLk]; exact Hlb)
        ?_ hk
      rcases Hv with rfl | rfl
      · exact List.ne_nil_of_length_pos (by rw [cvxLength]; omega)
      · exact List.ne_nil_of_length_pos (by simp)))
    (AxSpinApB.cpuWinP L GT i q S p _ Hpre H.hLk (by
      intro k lb rl m hk Hlb Hid
      have hkl := (List.getElem?_eq_some_iff.1 Hlb).1
      obtain ⟨lbH, HlbH, HsH⟩ := Prl 7 (.it (.RL (AxSpinT2a.zLk + 16) 8)) rfl
        (by simp only [relKh] at hk; omega)
      obtain ⟨aqH, HidH⟩ := HsH
      obtain ⟨tsH, vsH, HlH, HvsH⟩ : ∃ ts vs, lbH = .LLoad aqH (AxSpinT2a.zLk + 16) ts vs ∧
          vs.length = 8 := by
        cases lbH with
        | LLoad a b ts vs =>
          simp only [aident, AidentT.IRead.injEq] at HidH
          obtain ⟨rfl, rfl, h⟩ := HidH
          exact ⟨ts, vs, rfl, h⟩
        | _ => simp [aident] at HidH
      subst HlH
      obtain ⟨vw, cls', rfl, Hv⟩ := Hpre.2.2.2.2.2.2.1 k lb rl m Hlb (by rw [← H.hLk]; exact Hid)
      refine AxSpinRl2.lobpCpuLd GT Hcons (L.xlLk + 16) i _ k aqH tsH vsH vw cls'
        (by rw [H.hLk]; exact HlbH) (List.ne_nil_of_length_pos (by omega))
        (by rw [H.hLk]; exact Hlb) ?_ (by simp only [relKh] at hk ⊢; omega)
      rcases Hv with rfl | rfl
      · exact List.ne_nil_of_length_pos (by rw [cvxLength]; omega)
      · exact List.ne_nil_of_length_pos (by simp)))
    (fun hk => by
      obtain ⟨lb, Hlb, vw, rfl, -⟩ := Prl 17 (.RSc AxSpinT2a.zLk 4 .WCrel) (by cases q.c <;> rfl)
        (by simp only [relKw] at hk; omega)
      have Hz := Hpre.2.2.2.2.2.2.2.1 vw .WCrel Hlb
      rw [H.hLk, ← Hz]
      exact Hlb)
    (AxSpinApB.relWinCP Hpre H.lay L H.hLk)
    (by omega) (fun _ => ⟨lbS, HlbS, by rw [HlS]; rfl⟩)
    HP.rhRets.1 HP.rhRets.2
    (fun h12 => by
      rw [EJ4, AxSpinT2a.mycpuRetHart]
      obtain ⟨vs, hv, hl⟩ := AxSpinApB.gvRd _ i _ _ _ (RdL (by simp only [relKh] at h12 ⊢; omega))
      have G := HG .rlL (by simp only [cutPos, t2KRh, relKh] at h12 ⊢; omega) vs
        (by rw [← AxSpinT2f.gvGrow]; exact hv)
      rw [show relKh (t2KRl q) + 4 = t2KRh q + 4 from rfl, hv, ← G, AxSpinApB.st8 vs hl])
    (by rw [EJ10]; exact HP.rhS1)
    HP.ppMy
    (fun h vn hv => HG .ppN (by simp only [cutPos, t2KPp] at h ⊢; omega) vn
      (by rw [← AxSpinT2f.gvGrow]; exact hv))
    HP.ppArm
    (fun hc h vi hv => HG .ppI (by simp only [cutPos, t2KPp] at h ⊢; omega) hc vi
      (by rw [← AxSpinT2f.gvGrow]; exact hv))
    HP.ppRet
    (by
      simp only [AxSpinPO5.rlOk4]
      refine ⟨HlN, AxSpinT2h.stBytes4Len _, by simp only [relKp]; omega, ?_⟩
      rw [hpn]
      exact AxSpinApB.noffNowr Hpre H.lay)
    (fun _ => by
      cases hqb : q.b with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, AxSpinPO5.rlOk4]
      | true =>
        simp only [↓reduceIte, AxSpinPO5.rlOk4]
        refine ⟨HlI hqb, AxSpinT2h.stBytes4Len _, by unfold t2KPo; simp only [relKp]; omega, ?_⟩
        rw [hpi]
        exact AxSpinApB.intenaNowr Hpre H.lay)
    HP.rlRet AxSpinT2a.jalrRets.2.2.2.2.2.2
    (fun k' h1 h2 h3 h4 h5 h6 h7 pr => AxSpinApB.hookP L GT nm i q k'
      (by simp only [t2Len, t2KT]; omega) (fun _ => by omega)
      (fun he => by
        cases hbR with
        | false => exact absurd he (h3 rfl)
        | true => exact AxSpinApB.gateRlSOf HbR1)
      h4 h5 h6 h7 pr)
    (fun _ => by
      iintro -
      iapply (cutRelS L GT nm Hcons i (relKh (t2KRl q)) (t2KA q) (t2KMy q + 4)
        (AxSpinE8.mycpuRet (hartId (cpuOf i))) iprop(True) iprop(True)
        (AxSpinApB.t2PostP (gtAdGd GT) L nm i q)
        (fun h => by rw [H.hLk]; exact RdS h)
        (fun hL hg s => AxSpinApB.postCut (gtAdGd GT) L nm i q .rlS (by rw [hL]; rfl)
          (AxSpinT2h.gateRlS _ i q hg) s)))
    (fun _ rs _ _ => by
      iintro -
      iapply (cutRelL L GT nm Hcons i (relKh (t2KRl q)) (t2KA q) (t2KMy q + 4) rs
        (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
        (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
        (AxSpinE8.mycpuRet (hartId (cpuOf i))) iprop(True) iprop(True)
        (AxSpinApB.t2PostP (gtAdGd GT) L nm i q)
        (AxSpinT2a.mycpuRetHart _)
        (fun h => by rw [H.hLk]; exact RdL h)
        (fun hL hg s => AxSpinApB.postCut (gtAdGd GT) L nm i q .rlL (by rw [hL]; rfl)
          (AxSpinT2h.gateRlL _ i q hg) s)))
    (cutPpNF L GT nm Hcons i (t2KPp q) (t2KPo + 7) (t2KPoT q + 4)
      (BitVec.ofInt 64 (cpuZ i + 120)) _ (t2KPoT q + 5) clsN vp v _ hpn Himg rfl
      (by unfold t2KPoT t2KPo at P9 ⊢; omega) (by rw [hpn]; exact RdN2) HgvN
      (fun h => by rw [hpn]; exact Rd6 h)
      (fun hL hg s => AxSpinApB.postCut (gtAdGd GT) L nm i q .ppN (by rw [hL]; rfl)
        (AxSpinT2h.gatePpN _ i q hg) s))
    (fun hc => cutPpIF L GT nm Hcons i (t2KPp q) (t2KPo + 7) (t2KPoT q + 4) q.c q.b
      (BitVec.ofInt 64 (cpuZ i + 120)) (BitVec.ofInt 64 (cpuZ i + 124)) _ _ (t2KPoT q + 5) clsN
      (t2KPo + 12) clsI vn0 vp v _ hpn Himg rfl (fun hb => by simp only [hb, ↓reduceIte])
      (by unfold t2KPoT t2KPo; omega) (by unfold t2KPoT t2KPo at P9 ⊢; omega)
      (by rw [hpn]; exact Rd1) Hgv1 (HP.poArm vn0 Hgv1)
      (by rw [hpn]; exact RdN2) HgvN HP.ppArm (fun h => by rw [hpn]; exact Rd6 h)
      (fun h => by rw [hpi]; exact Rd8 hc h)
      (fun hL hg s => AxSpinApB.postCut (gtAdGd GT) L nm i q .ppI (by rw [hL]; rfl)
        (AxSpinT2h.gatePpI _ i q q.c hg rfl) s) hc))
    $$ Hil HLK HW HNp HGF
  iintro %vra %vs0 %vs1 %rs1 %ib1 %Hf - - - - - - -
  obtain ⟨Hc1, HPC1, Htl1, -, -, -, -, -, -, -, E91, Hkeep1, -, -, Hgd2, -, -, Hgv2⟩ := Hf
  have Evs1 : vs1 = stBytes 8 (BitVec.ofInt 64 p) := by
    have h := HP.rlS1 (AxSpinRl4.gvLt _ _ _ _ Hgv2)
    rw [show t2KRr q = relKr (t2KRl q) q.c from rfl, Hgv2, Hgd2, EJ9] at h
    exact Option.some.inj h
  rw [Evs1, AxSpinE8.ldResStBytes8] at E91
  have E131 : gprVal rs1 13#5 = gprVal rsR 13#5 :=
    (Hkeep1 13#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      EJ13
  have Htl1' : rs1 .tlb = rsR .tlb := Htl1.trans HtlJ
  have Hw1 := AxSpinApA.warmTlb rsR rs1 i S p Htl1' Hw
  -- row end at relKe
  by_cases Ee : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKe (t2KRl q) q.c
  · iclear K
    iapply (AxSpinApB.hookP L GT nm i q _ (by omega) (fun _ => by omega)
      (fun h => absurd h (by omega)) (by omega) (by omega) (fun _ => by omega) Ee _)
  -- ---- + 0x98: c.li a5,1 (t2KT) ----
  iapply (XR _ rs1 (relKe (t2KRl q) q.c) (pca 0x98) true ap98 none _
    (retxRefl cpu rs1 (relKe (t2KRl q) q.c) ib1) Hc1 HPC1
    (AxSpinApA.hitTxt rs1 Hw1 _ (by decide) (by decide))
    (AxSpinApA.atok98 σi T satp0 H.txt) (AxSpinE8.owOkSome 15#5 _ (by decide)) AxSpinApA.rfFAp98
    (certAddi _ rs1 (pca 0x98) true (zero_extend (m := 5) 0b00#2) 15#5
      (sign_extend (m := 12) (1#6)) (by decide)) (by omega))
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 (fun _ => rfl) HG2
  have HPC2 : rs2 .PC = pca 0x9a := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rsR .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1'
  have Hw2 := AxSpinApA.warmTlb rsR rs2 i S p Htl2 Hw
  have E92 : gprVal rs2 9#5 = BitVec.ofInt 64 p := by rw [HF2]; ax_spin_apb_zsimp; exact E91
  have E132 : gprVal rs2 13#5 = gprVal rsR 13#5 := by rw [HF2]; ax_spin_apb_zsimp; exact E131
  have Eva : gprVal rs2 9#5 + sign_extend (m := 64) 24#12 = BitVec.ofInt 64 (p + 24) := by
    rw [E92]; exact AxSpinApA.vaEq _ _ _ _ AxSpinApA.i24Of rfl
  ihave Fp := FstMPriv (hlc := hlc) (GF := GF) L GT nm HL Hcons i
    (paZ (BitVec.ofInt 64 (p + 24))) 4
    (by
      intro j hj
      rw [AxSpinApA.paZOf (p + 24) (by omega) (by omega)]
      exact H.hpriv _ (.inr (.inl ⟨by omega, by omega⟩)))
    (by
      rw [AxSpinApA.paZOf (p + 24) (by omega) (by omega)]
      exact AxSpinApB.wle4P Hpre H.lay _ (.inr (.inr (.inr rfl))))
  -- ---- + 0x9a: c.sw a5,24(s1) — THE TERMINAL PRIVATE STORE (t2KT) ----
  iapply (XS _ rs2 (relKe (t2KRl q) q.c) (pca 0x9a) true 24#12 15#5 9#5 4
    (gprVal rs2 9#5 + sign_extend (m := 64) 24#12) (BitVec.ofInt 64 (p + 24))
    (fun _ _ => iprop(True))
    (retxRefl cpu rs2 (relKe (t2KRl q) q.c) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (AxSpinApA.hitTxt rs2 Hw2 _ (by decide) (by decide))
    (AxSpinApA.atok9a σi T satp0 H.txt) AxSpinAp9.vw4 (by decide) (by decide) rfl
    (by rw [Eva]
        exact AxSpinApB.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inr
          (.inr ⟨by omega, by omega⟩)))))
    (by rw [Eva]
        refine Hw2 _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl ?_)))))))
        rw [AxSpinApA.toNatOf _ (by omega) (by omega)]
        omega)
    (by omega))
    $$ Fp
  iintro %rs3 %ib3 %HG3 %- -
  rw [show relKe (t2KRl q) q.c + 1 = t2Len q from rfl]
  iapply K $$ %rs3 %ib3
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG3, ?_, (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2, ?_,
    by omega⟩
  · rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  · rw [stepRegs0 T satp0 _ rs2 _ _ _ rs3 (fun _ => rfl) HG3]; exact E132


set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn in
/-- THE CRITICAL-SECTION PIECE on a PREFIX row: from acquire's return (allocproc + 0x44, row
position `t2KBd q`) through `wpdAllocpidCsP` (window `[t2KBd, t2KRl]`, no designated cut) and
`AxSpinApB.segRelP`; at the complete row end the two annotations (`npSrc`, `FRAG`) are read
back (`AxSpinApA.wpdEnd2`) into `t2PostP`. -/
theorem AxSpinApB.segCsP (q : T2Prm) (S p : Int) (H : AxSpinApB.Hyp2 L GT σi T i q S p)
    (rsC : RegFile) (ibC : Ibch) (cls clsN clsI : WmClass) (vp : List (BitVec 8)) :
    ctrlOkSW T satp0 rsC → rsC .PC = pca 0x44 → AxSpinApA.Warm rsC i S p →
    gprVal rsC 2#5 = BitVec.ofInt 64 S → gprVal rsC 4#5 = hartId (cpuOf i) →
    gprVal rsC 9#5 = BitVec.ofInt 64 p →
    (AxOpsem.grow (gtAdGd GT) i)[t2KMy q + 4]? = some (.LStore false (L.xlLk + 16)
      (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i)))) cls) →
    (AxOpsem.grow (gtAdGd GT) i)[t2KPoT q + 5]? = some (.LStore false
      (paZ (BitVec.ofInt 64 (cpuZ i + 120))) (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vp)))
      clsN) →
    (q.b = true → (AxOpsem.grow (gtAdGd GT) i)[t2KPo + 12]? = some (.LStore false
      (paZ (BitVec.ofInt 64 (cpuZ i + 124))) (stBytes 4 0#64) clsI)) →
    graphValue (gtAdGd GT) (i, t2KPoT q + 4) = some vp →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, t2KA q) (locked nm.xnReg L.xlLk i (i, t2KA q)) -∗
      AxAnnot.annotOwn (i, t2KA q) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, t2KA q)) -∗
      AxAnnot.annotOwn (GF := GF) (i, t2KMy q + 4)
        iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, t2KMy q + 4)
          (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (hartId (cpuOf i))))) -∗
      AxSpinT2h.genF (GF := GF) GT i (paZ (BitVec.ofInt 64 (cpuZ i + 120))) (t2KPo + 7)
        (t2KPoT q + 4) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsC none ibC, t2KBd q⟩ (AxSpinApB.t2PostP (gtAdGd GT) L nm i q) := by
  intro Hc HPC Hw E2 E4 E9 Hkw HlN HlI HgvN
  have Hpre := H.pre
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := AxSpinApA.nums H.lay
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, P10⟩ := AxSpinApB.posF q
  obtain ⟨K1, K2, K3, K4, K5, K6, K7, K8, K9⟩ := AxSpinT2f.kEqs q
  have hproc : (KernelSyms.«proc» : Int) = 0x80012930 := rfl
  have hBd := AxSpinT2a.kBdLen q
  have HP := H.pins
  obtain ⟨-, -, -, -, -, Pbd, -, -⟩ := AxSpinT2f.segPartsP Hpre.1
  have HΦmid := AxSpinApB.postSMidP (GF := GF) L GT nm i q
  have Eva : gprVal rsC 9#5 + sign_extend (m := 64) 48#12 = BitVec.ofInt 64 (p + 48) := by
    rw [E9]; exact AxSpinApA.vaEq _ _ _ _ AxSpinApA.i48Of rfl
  ihave Fp := FstMPriv (hlc := hlc) (GF := GF) L GT nm HL Hcons i
    (paZ (BitVec.ofInt 64 (p + 48))) 4
    (by
      intro j hj
      rw [AxSpinApA.paZOf (p + 48) (by omega) (by omega)]
      exact H.hpriv _ (.inr (.inr (.inl ⟨by omega, by omega⟩))))
    (by
      rw [AxSpinApA.paZOf (p + 48) (by omega) (by omega)]
      exact AxSpinApB.wle4P Hpre H.lay _ (.inr (.inr (.inl rfl))))
  iintro #Hil HLK HRN HW HGF
  iapply (wpdAllocpidCsP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix H.txc _ HΦmid
    (t2KBd q) rsC ibC vaNp (BitVec.ofInt 64 (p + 48)) AxSpinAp9.scanVa (i, t2KA q)
    (fun _ _ => iprop(True))
    (by rw [AxSpinApA.npOf]; ax_spin_apb_pz
        exact ⟨Pbd, Hpre.2.2.2.2.1.1, Hpre.2.2.2.2.1.2⟩)
    (by
      rw [AxSpinApA.npOf]
      ax_spin_apb_pz
      exact AxSpinApB.npOnlyP Hpre H.lay)
    (fun _ => by
      intro w a v' Ha Hwb Hpo
      exfalso
      obtain ⟨lb, rl, b, m, t, Hlb, Hid, Ht, Hab⟩ := AxSpinApA.gwbRow _ w _ _ Hwb
      obtain ⟨hw1, hw2, -, -⟩ := Hpo
      simp only at hw1 hw2
      rw [hw1] at Hlb
      have := AxSpinApB.npBeforeP Hpre H.lay w.2 lb rl b m hw2 Hlb Hid
      unfold npb at Ha
      rw [inClr, H.hNp] at Ha
      unfold dj at this
      omega)
    HP.npNowrap HP.npNcoll Hc HPC (AxSpinApA.hitTxt rsC Hw _ (by decide) (by decide))
    (by rw [AxSpinApA.npOf, H.hNp]; ax_spin_apb_pz)
    (by rw [AxSpinApA.npOf]; ax_spin_apb_pz; exact AxSpinApB.ntxOf H _ (by omega))
    (by rw [AxSpinApA.npOf]
        exact AxSpinApB.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))
    (by rw [AxSpinApA.npOf]
        exact AxSpinApB.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))
    (Hw _ (t2TouchNp i S p))
    (by
      intro j hj
      rw [AxSpinApA.scanOf j hj]
      have hsa : AxSpinAp7.scanAddr j = 0x80012930 + 376 * (j : Int) + 48 := by
        unfold AxSpinAp7.scanAddr; rw [hproc]
      refine ⟨AxSpinApB.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))),
        AxSpinApA.paZOf _ (by omega) (by omega), ?_⟩
      rw [← AxSpinApA.scanOf j hj]
      exact Hw _ (t2TouchScan i S p j hj))
    (by rw [Eva]
        exact AxSpinApB.dat H _ (.inr (.inl rfl)) _ 4 (.inl rfl) (by omega)
          (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))))
    (by rw [Eva]
        refine Hw _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr ?_)))))))
        rw [AxSpinApA.toNatOf _ (by omega) (by omega)]
        omega)
    (fun hk => by
      obtain ⟨tA, rvsA, HrmA, -⟩ := Hpre.2.2.2.2.2.1 q.n (Nat.le_refl _) (by omega)
      obtain ⟨lbR, HlbR, aqR, HidR⟩ := Pbd 0 (.RL AxSpinT2a.zNp 4) rfl (by omega)
      rw [Nat.add_zero] at HlbR
      have HmR : lbIsMem lbR = true := by
        cases lbR with
        | LLoad => rfl
        | _ => simp [aident] at HidR
      exact AxSpinRl2.lobpAcq GT Hcons i (t2KA q) (t2KBd q) _ lbR AxSpinT2a.zLk 4 HrmA rfl HlbR
        HmR (by omega))
    (fun k' h1 h2 h3 pr => AxSpinApB.hookP L GT nm i q k' (by omega)
      (fun hb => by
        have : holdLen q.hb = 12 := by simp [holdLen, hb]
        omega)
      (fun he => absurd he (by omega)) (by omega) (by omega) (fun _ => by omega) h3 pr))
    $$ HRN Fp
  iintro %vs %rs1 %ib1 %Hf Hsrc HRN65 HFR -
  obtain ⟨Hc1, HPC1, Htl1, -, -, E131, -, -, E101, -, -, Hkeep1, -, Hgd66⟩ := Hf
  have Hw1 := AxSpinApA.warmTlb rsC rs1 i S p Htl1 Hw
  rw [show t2KBd q + 67 = t2KRl q from rfl]
  iapply (AxSpinApB.segRelP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu q S p H
    rs1 ib1 cls clsN clsI vp Hc1 HPC1 Hw1
    ((Hkeep1 2#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E2)
    ((Hkeep1 4#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E4)
    ((Hkeep1 9#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E9)
    E101 Hkw HlN HlI HgvN) $$ Hil HLK HW HRN65 HGF
  iintro %rs2 %ib2 %Hf2
  obtain ⟨-, -, -, -, hlen⟩ := Hf2
  -- THE COMPLETE ROW END: read back the nextpid source and the issued fragment
  ihave W := (AxSpinApA.wpdEnd2 L GT nm i (t2Len q) (by omega) (i, t2KBd q) (i, t2KBd q + 65)
    rfl rfl (by intro h; have := congrArg Prod.snd h; simp at this)
    iprop(⌜npSrc (gtAdGd GT).gdG L (i, t2KBd q) (i, t2KA q)⌝) (FRAG nm (wordOfBytes 4 vs))
    (AxSpinApB.t2PostP (gtAdGd GT) L nm i q)
    (by
      intro s
      unfold AxSpinApB.t2PostP
      iintro ⟨HF, %Hs⟩ %_
      isplitr
      · ipureintro
        exact notCutAtOfLen (fun j hj => by have := AxSpinT2f.cutPosLen j q; omega)
      · iintro %_
        iexists (wordOfBytes 4 vs)
        isplitr
        · ipureintro
          exact ⟨Hgd66, Hs⟩
        · iexact HF)) $$ Hsrc HFR
  iapply W

set_option maxHeartbeats 6400000 in
include HL Hcons hmode hasid hppn in
/-- **THE WHOLE-SEGMENT WPd ON PREFIX ROWS** (stage-2 design §C row `AxSpinApA (edit/new ApB)`):
hart `i`'s inlined allocpid from `allocproc + 0x38` (row position 0) on ANY row of the PREFIX
family (`AxSpinApB.Hyp2`: `allocPre`, the guarded pins `AllocPins2`, the noff image premise),
`WPd {{ AxSpinApB.t2PostP }}`: at every non-mid state the row is NO CUT ROW (the five designated
cuts — acquire's `aq`, release's `rlS`/`rlL`, pop_off's `ppN`/`ppI` — are refuted by D4 readback
in AxSpinT2h's arms), and a COMPLETE row gives the stage-1 post (pid, `npSrc`, `FRAG`).
Compositions: `AxSpinAq2.wpdAcquireP` (cut `aq` ← `cutAq`), `wpdAllocpidCsP`, `wpdReleaseP`
(cuts ← `cutRelS`/`cutRelL`/`cutPpNF`/`cutPpIF`, push_off's genesis annotations as the frame);
every other row end is the resource-free hook `AxSpinApB.hookP`.  Explicit premises beyond the
bundle: the lk->cpu image is 0 (`Himgc`), its writers are harts (`Hwlt`), and — OWNER QUESTION
Q-S2-B (byte mixing) OPEN — `HsrcAl` (`AxSpinT2g.clSrcAligned` at acquire's racy `ld lk->cpu`). -/
theorem wpdAllocpidSeg2 (q : T2Prm) (S p : Int) (H : AxSpinApB.Hyp2 L GT σi T i q S p)
    (Himgc : ∀ a, a ∈ clb L → (gtAdGd GT).gdG.gxImg a = some b0)
    (Hwlt : ∀ w a v, a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v → w.1 < NCPU)
    -- OWNER QUESTION Q-S2-B (byte mixing): the racy read's lk->cpu sources are full-width
    (HsrcAl : AxSpinT2g.clSrcAligned (clb L) (gtAdGd GT).gdG (i, t2KHd q + 4))
    (rs0 : RegFile) (ib0 : Ibch) :
    ctrlOkSW T satp0 rs0 → rs0 .PC = pca 0x38 → AxSpinApA.Warm rs0 i S p →
    gprVal rs0 2#5 = BitVec.ofInt 64 S → gprVal rs0 4#5 = hartId (cpuOf i) →
    gprVal rs0 9#5 = BitVec.ofInt 64 p →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, 0⟩ (AxSpinApB.t2PostP (gtAdGd GT) L nm i q) := by
  intro Hc HPC Hw E2 E4 E9
  have Hpre := H.pre
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := AxSpinApA.nums H.lay
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, P10⟩ := AxSpinApB.posF q
  obtain ⟨K1, K2, K3, K4, K5, K6, K7, K8, K9⟩ := AxSpinT2f.kEqs q
  have hBd := AxSpinT2a.kBdLen q
  have hpn : paZ (BitVec.ofInt 64 (cpuZ i + 120)) = cpuZ i + 120 :=
    AxSpinApA.paZOf _ (by omega) (by omega)
  have HG := Hpre.2.2.2.2.2.2.2.2
  have HP := H.pins
  obtain ⟨-, -, Phd, -, -, -, -, -⟩ := AxSpinT2f.segPartsP Hpre.1
  have HΦmid := AxSpinApB.postSMidP (GF := GF) L GT nm i q
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix _ HΦmid
  have RdA : q.hb = true → t2KHd q + 4 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (t2KHd q + 4) (AxSpinT2a.zLk + 16) 8 :=
    fun hbt h => by
      have Phd' := Phd
      rw [hbt] at Phd'
      exact AxSpinApB.rdOfP Phd' (j := 4) rfl h
  iintro #Hil Hnh
  -- row end at 0
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ 0
  · iclear Hnh
    iapply (AxSpinApB.hookP L GT nm i q 0 (by omega) (fun _ => by omega)
      (fun h => absurd h (by omega)) (by omega) (by omega) (fun _ => by omega) E0 _)
  have hl0 : 0 < (AxOpsem.grow (gtAdGd GT) i).length := by omega
  -- ---- + 0x38: auipc a0,0x11 (row 0) ----
  iapply (XR _ rs0 0 (pca 0x38) false ap38 none (some (10#5, pca 0x38 + auipcOff 17#20))
    (retxRefl cpu rs0 0 ib0) Hc HPC (AxSpinApA.hitTxt rs0 Hw _ (by decide) (by decide))
    (atok38 σi T satp0 H.txc) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFAp38
    (certAuipc _ rs0 (pca 0x38) false 10#5 17#20 (by decide)) hl0)
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pca 0x3c := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- ---- + 0x3c: addi a0,a0,-1706 (a0 = &pid_lock) ----
  have Hc2 : CertC (ctrlOkSW T satp0) rs1 (pca 0x3c) false ap3c none
      (some (10#5, BitVec.ofNat 64 KernelSyms.«pid_lock»)) := by
    have h := certAddi (ctrlOkSW T satp0) rs1 (pca 0x3c) false 10#5 10#5 0x956#12 (by decide)
    simp only [HF1] at h
    ax_spin_apb_zsimp at h
    rw [AxSpinApA.a0Entry] at h
    exact h
  iapply (XR _ rs1 0 (pca 0x3c) false ap3c none _
    (retxRefl cpu rs1 0 ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (AxSpinApA.hitTxt rs1 (AxSpinApA.warmTlb rs0 rs1 i S p Htl1 Hw) _ (by decide) (by decide))
    (atok3c σi T satp0 H.txc) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFAp3c Hc2 hl0)
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = pca 0x40 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  -- ---- + 0x40: jal ra,acquire ----
  have Hcj : CertC (ctrlOkSW T satp0) rs2 (pca 0x40) false ap40 (some (AxSpinHdB.pac 0))
      (some (1#5, BitVec.addInt (pca 0x40) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs2 (pca 0x40)
      false 2093222#21 1#5 (by decide)
    rw [show pca 0x40 + sign_extend (m := 64) 2093222#21 = AxSpinHdB.pac 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (pca 0x40) (incr false)) =
      some (1#5, BitVec.addInt (pca 0x40) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs2 0 (pca 0x40) false ap40 (some (AxSpinHdB.pac 0))
    (some (1#5, BitVec.addInt (pca 0x40) (incr false)))
    (retxRefl cpu rs2 0 ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (AxSpinApA.hitTxt rs2 (AxSpinApA.warmTlb rs0 rs2 i S p Htl2 Hw) _ (by decide) (by decide))
    (atok40 σi T satp0 H.txc) (AxSpinE8.owOkSome 1#5 _ (by decide)) rfFAp40 Hcj hl0)
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = AxSpinHdB.pac 0 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; rfl
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  have Hc3 := gbCtrl T satp0 _ _ _ _ _ _ HG3
  have Hw3 := AxSpinApA.warmTlb rs0 rs3 i S p Htl3 Hw
  have E32 : gprVal rs3 AxSpinE8.r2 = BitVec.ofInt 64 S := by
    rw [HF3]; ax_spin_apb_zsimp; exact E2
  have E34 : gprVal rs3 AxSpinE8.r4 = hartId (cpuOf i) := by
    rw [HF3]; ax_spin_apb_zsimp; exact E4
  have E39 : gprVal rs3 9#5 = BitVec.ofInt 64 p := by
    rw [HF3]; ax_spin_apb_zsimp; exact E9
  have E310 : gprVal rs3 AxSpinE8.r10 = BitVec.ofNat 64 KernelSyms.«pid_lock» := by
    rw [HF3]; ax_spin_apb_zsimp
  -- ---- acquire (P-form; rows 0 .. t2KMy q + 8) ----
  iapply (AxSpinAq2.wpdAcquireP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu H.fix H.txa
    H.txm H.txp H.txh _ HΦmid 0 q.b q.hb q.n rs3 ib3 (pca 0x44)
    (BitVec.ofInt 64 (S - 8)) (BitVec.ofInt 64 (S - 16)) (BitVec.ofInt 64 (S - 24))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
    (BitVec.ofInt 64 (cpuZ i + 120)) (BitVec.ofInt 64 (cpuZ i + 124))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
    (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
    (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48))
    (BitVec.ofInt 64 (AxSpinT2a.zLk + 16)) (BitVec.ofInt 64 AxSpinT2a.zLk)
    (by rw [H.hLk]; ax_spin_apb_pz; exact AxSpinApB.acqP Hpre)
    (by rw [H.hLk]; exact Hpre.2.2.2.2.2.1) Hpre.2.2.2.1 (AxSpinApB.w8P Hpre)
    (fun _ _ => AxSpinApB.noRmw8P Hpre _)
    (by ax_spin_apb_pz; exact AxSpinApB.wle4P Hpre H.lay _ (.inl rfl))
    (AxSpinApB.noRmwnP Hpre _ 4 (.inl (by ax_spin_apb_pz; omega)))
    (by ax_spin_apb_pz; exact AxSpinApB.wle4P Hpre H.lay _ (.inr (.inl rfl)))
    (by
      intro k' lb aq rl m Hlb Hid
      obtain ⟨-, rfl⟩ := AxSpinApB.rmwP Hpre k' lb aq rl _ m Hlb Hid
      omega)
    (AxSpinApB.cpuWinP L GT i q S p _ Hpre H.hLk (by
      intro k lb rl m hk Hlb Hid
      have hkl := (List.getElem?_eq_some_iff.1 Hlb).1
      have hk' : t2KA q < k := hk
      obtain ⟨tA, rvsA, HrmA, -⟩ := Hpre.2.2.2.2.2.1 q.n (Nat.le_refl _) (by
        rw [← AxSpinT2a.kSpA]; omega)
      exact AxSpinRl2.lobpAcq GT Hcons i (t2KA q) k _ lb AxSpinT2a.zLk 4 HrmA rfl Hlb
        (AxSpinApA.wrMem lb _ Hid) hk))
    Hc3 HPC3 (AxSpinApA.hitTxt rs3 Hw3 _ (by decide) (by decide))
    (AxSpinApA.hitTxt rs3 Hw3 _ (by decide) (by decide))
    (by rw [H.hLk]; ax_spin_apb_pz)
    (by ax_spin_apb_pz; exact AxSpinApB.ntxOf H _ (by omega))
    (by rw [E310, AxSpinApA.lkOf]
        exact AxSpinApB.dat H _ (.inl rfl) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lkOf]
        exact AxSpinApB.dat H _ (.inr (.inr rfl)) _ 4 (.inl rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lkOf, show AxSpinT2a.zLk = AxSpinT2a.zLk + 0 by omega]
        exact AxSpinApA.hitLk rs3 Hw3 0 (by omega) (by omega))
    (by rw [H.hLk]; ax_spin_apb_pz)
    (by ax_spin_apb_pz; exact AxSpinApB.ntxOf H _ (by omega))
    (by rw [E310, AxSpinApA.lk16]
        exact AxSpinApB.dat H _ (.inl rfl) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lk16]
        exact AxSpinApB.dat H _ (.inr (.inl rfl)) _ 8 (.inr rfl) (by omega) (.inr (.inr (.inl
          ⟨by omega, by omega⟩))))
    (by rw [E310, AxSpinApA.lk16]; exact AxSpinApA.hitLk rs3 Hw3 16 (by omega) (by omega))
    (by rw [E32, AxSpinApA.aA24]; exact AxSpinApB.slot H rs3 Hw3 8 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aA16]; exact AxSpinApB.slot H rs3 Hw3 16 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aA8]; exact AxSpinApB.slot H rs3 Hw3 24 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQ24]; exact AxSpinApB.slot H rs3 Hw3 40 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQ16]; exact AxSpinApB.slot H rs3 Hw3 48 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQ8]; exact AxSpinApB.slot H rs3 Hw3 56 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm8]; exact AxSpinApB.slot H rs3 Hw3 72 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm0]; exact AxSpinApB.slot H rs3 Hw3 80 (by omega) (by omega) (by omega))
    (by rw [E34, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i120Of rfl]
        exact AxSpinApB.fld H rs3 Hw3 120 (.inl rfl))
    (by rw [E34, AxSpinApA.myOf, AxSpinApA.vaEq _ _ _ _ AxSpinApA.i124Of rfl]
        exact AxSpinApB.fld H rs3 Hw3 124 (.inr rfl))
    (by rw [E32, AxSpinApA.aH24]; exact AxSpinApB.slot H rs3 Hw3 40 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aH16]; exact AxSpinApB.slot H rs3 Hw3 48 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aH8]; exact AxSpinApB.slot H rs3 Hw3 56 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm8]; exact AxSpinApB.slot H rs3 Hw3 72 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aQm0]; exact AxSpinApB.slot H rs3 Hw3 80 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aM8]; exact AxSpinApB.slot H rs3 Hw3 40 (by omega) (by omega) (by omega))
    (by rw [E32, AxSpinApA.aM0]; exact AxSpinApB.slot H rs3 Hw3 48 (by omega) (by omega) (by omega))
    (by ax_spin_apb_pz; apply AxSpinApA.alldjOf; ax_spin_apb_dj)
    (by ax_spin_apb_pz; apply AxSpinApA.slotsDisjOf; ax_spin_apb_dj)
    (by ax_spin_apb_pz; unfold dj; omega)
    (by ax_spin_apb_pz; unfold dj; omega) (by ax_spin_apb_pz; unfold dj; omega)
    (by ax_spin_apb_pz; unfold dj; omega)
    (by
      rw [H.hLk]
      ax_spin_apb_pz
      simp only [AxSpinAq2.djOut, List.mem_cons, List.not_mem_nil, _root_.or_false,
        forall_eq_or_imp, forall_eq, dj]
      omega)
    HP.poMy1 HP.poArm HP.poMy2 HP.poMy3 HP.poRet (by rw [E310]; exact HP.poS1)
    (by
      intro hb
      obtain ⟨h7, h9⟩ := HP.hdRets hb
      refine ⟨h7, h9, by rw [E310]; exact HP.hdS1 hb, ?_⟩
      intro h12 vcpu Hv
      rw [E34, AxSpinT2a.mycpuRetHart]
      exact (AxSpinT2a.hresZero _ _).2 (HG .aq (by simp only [cutPos, t2KHd]; omega) hb vcpu
        (by rw [← AxSpinT2f.gvGrow]; exact Hv)))
    HP.aqMy HP.aqRet AxSpinT2a.jalrRets.2.2.2.1
    (fun hbt rsH => cutAq L GT nm Hcons i (aqKp 0 q.b) rsH
      (BitVec.ofInt 64 (S - 40)) (BitVec.ofInt 64 (S - 48)) (BitVec.ofInt 64 (S - 56))
      (BitVec.ofInt 64 (S - 72)) (BitVec.ofInt 64 (S - 80))
      (AxSpinApB.t2PostP (gtAdGd GT) L nm i q)
      (fun h => by rw [H.hLk]; exact RdA hbt h) Himgc H.lay.hi Hwlt
      (fun w a v Ha Hwb Hpo => by
        obtain ⟨lb, rl, b, m, t, Hlb, Hid, Ht, Hab⟩ := AxSpinApA.gwbRow _ w _ _ Hwb
        obtain ⟨hw1, hw2, -, -⟩ := Hpo
        simp only at hw1 hw2
        rw [hw1] at Hlb
        have := AxSpinApB.clbBefore Hpre H.lay w.2 lb rl b m hw2 Hlb Hid
        unfold clb at Ha
        rw [inClr, H.hLk] at Ha
        unfold dj at this
        omega)
      HsrcAl
      (fun hL hg s => AxSpinApB.postCut (gtAdGd GT) L nm i q .aq (by rw [hL]; rfl)
        (AxSpinT2h.gateAq _ i q hg) s))
    (fun k' h1 h2 h3 h4 pr => AxSpinApB.hookP L GT nm i q k'
      (by have h2' : k' ≤ t2KBd q := h2; omega) h3
      (fun he => absurd he (by have h2' : k' ≤ t2KBd q := h2; omega))
      (by have h2' : k' ≤ t2KBd q := h2; omega) (by have h2' : k' ≤ t2KBd q := h2; omega)
      (fun _ => by have h2' : k' ≤ t2KBd q := h2; omega) h4 pr)) $$ Hil Hnh
  unfold AxSpinAq2.KAcqP
  rw [E34, show aqKA 0 q.b q.hb q.n = t2KA q from rfl, show aqKm 0 q.b q.hb q.n = t2KMy q from rfl,
    show 0 + 3 + 8 + (if q.b then 5 else 0) = t2KPoT q from rfl,
    show 0 + 3 + 7 = t2KPo + 7 from rfl, show 0 + 3 + 12 = t2KPo + 12 from rfl]
  iintro %vn %vra' %vs0' %vs1' %rsC %ibC %Ht HLK HNp HDep - - - G1 G2
  obtain ⟨Hlbn, Hlbi, Hgvn, HcC, HPCC, HtlC, EspC, -, -, -, -, -, -, Es1C, HkeepC, -, -, Hgd2, -,
    -, Hlb4, -, -, Hgv7⟩ := Ht
  obtain ⟨cls, Hlb4⟩ := Hlb4
  obtain ⟨clsN, Hlbn⟩ := Hlbn
  obtain ⟨clsI, HlI⟩ : ∃ clsI : WmClass, q.b = true →
      (AxOpsem.grow (gtAdGd GT) i)[t2KPo + 12]? = some (.LStore false
        (paZ (BitVec.ofInt 64 (cpuZ i + 124))) (stBytes 4 0#64) clsI) := by
    cases hqb : q.b with
    | false => exact ⟨.WCplain, fun h => nomatch h⟩
    | true =>
      obtain ⟨c, hc⟩ := Hlbi hqb
      exact ⟨c, fun _ => hc⟩
  have Evs1 : vs1' = stBytes 8 (BitVec.ofInt 64 p) := by
    have h := HP.aqS1 (AxSpinRl4.gvLt _ _ _ _ Hgv7)
    rw [Hgv7, show ((i, 2) : Geid) = (i, 0 + 2) from rfl, Hgd2, E39] at h
    exact Option.some.inj h
  rw [Evs1, AxSpinE8.ldResStBytes8] at Es1C
  -- push_off's two genesis annotations: no row write before either noff read touches noff
  have NW1 : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (t2KPo + 7)
      (paZ (BitVec.ofInt 64 (cpuZ i + 120))) 4 := by
    rw [hpn]; exact AxSpinApB.noffNoWrB Hpre H.lay _ (by unfold t2KPoT t2KPo; omega)
  have NW2 : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (t2KPoT q + 4)
      (paZ (BitVec.ofInt 64 (cpuZ i + 120))) 4 := by
    rw [hpn]; exact AxSpinApB.noffNoWrB Hpre H.lay _ (by omega)
  ihave G1 := G1 $$ %NW1
  ihave G2 := G2 $$ %NW2
  rw [show t2KMy q + 8 = t2KBd q from rfl]
  iapply (AxSpinApB.segCsP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu q S p H
    rsC ibC cls clsN clsI vn HcC HPCC
    (AxSpinApA.warmTlb rs0 rsC i S p (HtlC.trans Htl3) Hw) (EspC.trans E32)
    ((HkeepC 4#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans E34)
    Es1C Hlb4 Hlbn HlI Hgvn) $$ Hil HLK HNp HDep [G1 G2]
  unfold AxSpinT2h.genF
  isplitl [G1]
  · iexact G1
  · iexact G2

end seg


/-! # 5. For the capstone (T2b2): entry, the real layout, bridges -/

section segE
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- `wpdAllocpidSeg2` from AxSpinT2a's `entryOk` (the capstone's `Hentry`). -/
theorem AxSpinApB.wpdAllocpidSeg2E (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) (i : Agent) (q : T2Prm)
    (S p : Int) (H : AxSpinApB.Hyp2 L GT σi T i q S p)
    (Himgc : ∀ a, a ∈ clb L → (gtAdGd GT).gdG.gxImg a = some b0)
    (Hwlt : ∀ w a v, a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v → w.1 < NCPU)
    -- OWNER QUESTION Q-S2-B (byte mixing)
    (HsrcAl : AxSpinT2g.clSrcAligned (clb L) (gtAdGd GT).gdG (i, t2KHd q + 4)) (s : Athread) :
    entryOk T satp0 i S p s →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s
        (AxSpinApB.t2PostP (gtAdGd GT) L nm i q) := by
  rintro ⟨rs, ib, rfl, Hc, HPC, E2, E9, E4, Hw⟩
  exact wpdAllocpidSeg2 L GT nm HL Hcons σi T satp0 hmode hasid hppn i (cpuOf i) q S p H Himgc
    Hwlt HsrcAl rs ib Hc HPC Hw E2 E4 E9

end segE

/-- `AxSpinApB.Hyp2` at the real layout `xlayXv6` (as `AxSpinApA.hypXv6`, on `allocPre` /
`AllocPins2` and the noff image premise `HimgNoff`). -/
theorem AxSpinApB.hypXv6P (A B C : Agent) (Sf pf : Agent → Int) (ptp : Int → Prop)
    (HLay : T2LayHyp A B C Sf pf ptp) (GT : GdexecT) (σi : ExecSt) (T : PTree) (i : Agent)
    (q : T2Prm) (hi : i = A ∨ i = B) (hal : Sf i % 16 = 0)
    (Hpre : allocPre (AxOpsem.grow (gtAdGd GT) i) q i (Sf i) (pf i))
    (HP : AllocPins2 (gtAdGd GT) i q) (Himg : HimgNoff (gtAdGd GT).gdG.gxImg A B)
    (Hmap : AxSpinApA.MapOk σi T i (Sf i) (pf i))
    (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
    (Htxh : holdingText σi T) (Htxq : popOffText σi T) (Htxr : releaseText σi T)
    (Htxc : allocpidText σi T) (Htxt : AxSpinApA.tailText σi T)
    (Hfix : textFixed (gtAdGd GT) i (imgS σi)) :
    AxSpinApB.Hyp2 (xlayXv6 A B C Sf pf ptp) GT σi T i q (Sf i) (pf i) where
  pre := Hpre
  pins := HP
  imgN := Himg i (by rcases hi with rfl | rfl <;> simp)
  lay := ⟨AxSpinT2a.hartLt A B C Sf pf ptp HLay i (hi.elim .inl (fun h => .inr (.inl h))),
    (HLay.stk i (hi.elim .inl (fun h => .inr (.inl h)))).1,
    (HLay.stk i (hi.elim .inl (fun h => .inr (.inl h)))).2, hal,
    HLay.slot i (hi.elim .inl (fun h => .inr (.inl h)))⟩
  hLk := rfl
  hNp := rfl
  hpriv := fun a ha => (AxSpinT2a.privIff A B C Sf pf ptp a i).2
    ⟨by rcases hi with h | h <;> simp [h], ha⟩
  ntx := fun _ h => h
  map := Hmap
  txa := Htxa
  txm := Htxm
  txp := Htxp
  txh := Htxh
  txq := Htxq
  txr := Htxr
  txc := Htxc
  txt := Htxt
  fix := Hfix

/-- Stage 1's bundle (with the five gates from stage 1's pins) is a stage-2 bundle, given the
noff image premise. -/
theorem AxSpinApB.hyp2OfHyp {L : Xlay} {GT : GdexecT} {σi : ExecSt} {T : PTree} {i : Agent}
    {q : T2Prm} {S p : Int} (H : AxSpinApA.Hyp L GT σi T i q S p)
    (Himg : ∃ v, noffImgOk (gtAdGd GT).gdG.gxImg i v) : AxSpinApB.Hyp2 L GT σi T i q S p where
  pre := preOfFullPins H.full H.pins
  pins := pins2OfPins H.pins
  imgN := Himg
  lay := H.lay
  hLk := H.hLk
  hNp := H.hNp
  hpriv := H.hpriv
  ntx := H.ntx
  map := H.map
  txa := H.txa
  txm := H.txm
  txp := H.txp
  txh := H.txh
  txq := H.txq
  txr := H.txr
  txc := H.txc
  txt := H.txt
  fix := H.fix

/-- The post's cut conjunct (q-indexed) gives the design's `¬ t2Cut` (determinacy, `cutDet`). -/
theorem AxSpinApB.notCutOfAt {GD : Gdexec} {i : Agent} {q : T2Prm} {S p : Int}
    (H : allocPre (AxOpsem.grow GD i) q i S p) (h : ¬ t2CutAt (AxOpsem.grow GD i) q i) :
    ¬ t2Cut GD i S p :=
  fun ⟨_, H', Hc⟩ => h (cutDet H H' Hc)

end Weak
