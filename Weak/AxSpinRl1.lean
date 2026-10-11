/-
Weak: **ROW SHAPE of xv6's REAL `release`** (pure) — Theorem 2 design (`notes/weak-lb-thm2-design.md`
§C.2, §D row `AxSpinRl1`) / step-3 plan [ID-1], [ID-6].  NEW Lean file (no Rocq source: Rocq's
`AxSpinRs`/`AxSpinRl*` were never written).

## What this file provides (the interface of AxSpinRl2..4 and AxSpinT2a)

§1 THE EXTENDED SHAPE LANGUAGE `Rxitem`.  `Ritem` (AxSpinPOr) is a closed inductive of a merged
   file, so instead of adding the plan's `Ritem.RB` / `Ritem.RSc` arms we WRAP it:
   `Rxitem.it i` (any `Ritem`), `Rxitem.RB pr pw sr sw` (a fence: `aident lb = .IFence pr pw sr sw`),
   `Rxitem.RSc pa n cls` (a plain `n`-byte store at `pa` with PINNED class `cls`), and
   `Rxitem.RM aq rl pa n` (an RMW: `aident lb = .IRmw aq rl pa n` — acquire's amoswap, so that
   T2a's `allocSeg` can be one `List Rxitem`).  `RowShX k row sh` is `RowSh` over `xshape`;
   `rowShXMap : RowShX k row (sh.map .it) ↔ RowSh k row sh` embeds every existing window;
   `rowShXAppL/AppR/Len/Nowr` are the generic facts; `rowSpinOfX` turns a replicated `RM` window
   into AxSpinAqr's `RowSpin`.
§2 HOLDING'S WINDOW AS A LIST (plan ID-1 `Row_holding_of`): `holdShB hb …` (12 / 1 items) and
   `rowHoldingOf : RowSh k row (holdShB hb …) → lkBranch row k hb → k + holdLen hb < row.length →
   RowHolding k row hb …` (AxSpinHd8).
§3 `relSh c …` and the positions.  `k` = release's first memory event (Stage C: fetches have no
   item).  Cross-checked against `Xv6/KernelImage.lean` (release = 0x80000ce0):
     k+0..2   `relHead`: c.sdsp ra/s0/s1 at +0x02/+0x04/+0x06 (0xec06, 0xe822, 0xe426)
     relKh k = k+3   holding's window `holdShB true` (jal holding at +0x0c, 0xf07ff0ef), 12 items
                     (c.beqz a0 at +0x10, 0xcd11: no event)
     relKc k = k+15  `sd zero,16(s1)` at +0x12 (0x0004b823): `RS pcl 8`
     relKf k = k+16  `fence rw,w` at +0x16 (0x0310000f): `RB true true false true`
     relKw k = k+17  `sw zero,0(s1)` at +0x1a (0x0004a023): `RSc plk 4 WCrel`
     relKp k = k+18  `ppSh c` (jal pop_off at +0x1e, 0xf9bff0ef), `ppLen c` = 10 / 11 items
     relKr k c = relKp k + ppLen c   `relTail`: c.ldsp ra/s0/s1 at +0x22/+0x24/+0x26
                     (0x60e2, 0x6442, 0x64a2); c.addi16sp +0x28, c.ret +0x2a: no event
     relKe k c = relKr k c + 3      the boundary after the c.ret (= k + relLen c)
   `RowRelease k c row … := RowShX k row (relSh c …) ∧ lkBranch row (relKh k) true ∧
   relKe k c < row.length` (the boundary after the c.ret needs a next row item, as `XxRet`).
   Projections for the composer: `rowReleaseHead`, `rowReleaseHolding`, `rowReleaseCpu`,
   `rowReleaseFence`, `rowReleaseRel`, `rowReleasePop`, `rowReleaseTail`, `rowReleaseLen`,
   `rowReleaseNowr` (the three spills are not overwritten before their reloads).
§4 HONESTY OF THE PINNED CLASS (ID-6).  `relpLb` moves the release-pending flag along ROW labels
   exactly as `AxClsStep.relpUpd` moves it along program labels (fence with `pw ∧ sw` arms it,
   every store / RMW clears it, loads keep it); `relpAt row k` = the flag before item `k`;
   `rowClsHonest row`: every store's class is `WCrel` iff `rl ∨ relpAt` (else `WCplain`), every
   RMW's is `WCexcl` — `wmClassOf`'s formula (`akSync` = the label's `rl`, AxEpiRun; RMWs are
   `akLatest`), i.e. `AxClsStep.clsStep`'s class condition read on the row.  `rowReleaseRelp`:
   in a release row the flag IS set at `relKw` (so the pinned `WCrel` is the honest class there,
   `rowReleaseRelHonest`) and cleared right after (`rowReleaseRelpClear`).  `rowClsOkB` is a
   Bool checker with soundness `rowClsHonestOfB`, for the per-certificate discharge (ID-9,
   `decide +kernel` on literal rows).

HONESTY.  Everything here is pure row bookkeeping: `RowRelease` fixes which positions are loads,
stores, the fence and their addresses/classes; it says NOTHING about values (the panic arm of
`c.beqz a0` and pop_off's arms are graph-value pins of AxSpinRl4 / AxSpinPO6, Option V).
`rowClsHonest` is a property the certificates must establish; it is not derived from the
program here (the ∀-row lemma is a follow-up, as in the step-3 plan ID-9).  The step-relation
side: `relpUpd` also has non-memory arms (LRegW, LCtrl, LIFetch, …) which keep the flag; they
emit no row item, so `relpAt` agrees with `relpUpd` folded over the program labels of a run
(not proved here).

## Deviations from the design
1. `Ritem` is NOT edited (merged file): the plan's `Ritem.RB`/`RSc` are `Rxitem.RB`/`RSc` of a
   wrapper type, plus `Rxitem.RM` (not in the plan; T2a's spin items).  Old windows enter as
   `sh.map .it` (`rowShXMap`).
2. `relSh` contains holding's window as the list `holdShB true …` (the plan says `RowHolding
   true`, a Prop); `rowHoldingOf` recovers `RowHolding`.

**Reused:** `Ritem`/`ishape`/`RowSh`/`itDisj`/`dj`/`nowr`/`mycSh`/`ppSh`/`rowMycpuOf`/
`lookup_app_l_Some` (AxSpinPOr, AxSpinPO6, MachCSL.StdppList), `RowHolding`/`lkBranch`
(AxSpinHd8), `RowSpin`/`rmwAt` (AxSpinAqr), `lbCls` (WeakAxiomatic).  All names are new
(grepped absent from the tree).
-/
import Weak.AxSpinAqr
import Weak.AxSpinPO6

namespace Weak

open MachCSL MachCSL.Stdpp

/-! # 1. The extended shape language -/

/-- A row item: an old `Ritem`, a fence, a class-pinned plain store, or an RMW. -/
inductive Rxitem where
  | it (i : Ritem)
  | RB (pr pw sr sw : Bool)
  | RSc (pa : Int) (n : Nat) (cls : WmClass)
  | RM (aq rl : Bool) (pa : Int) (n : Nat)

/-- What a row label must look like to match an `Rxitem`. -/
def xshape (x : Rxitem) (lb : Lbl) : Prop :=
  match x with
  | .it i => ishape i lb
  | .RB pr pw sr sw => aident lb = .IFence pr pw sr sw
  | .RSc pa n cls => ∃ vw, lb = .LStore false pa vw cls ∧ vw.length = n
  | .RM aq rl pa n => aident lb = .IRmw aq rl pa n

/-- `RowSh` over `xshape`. -/
def RowShX (k : Nat) (row : List Lbl) (sh : List Rxitem) : Prop :=
  ∀ j x, sh[j]? = some x → ∃ lb, row[k + j]? = some lb ∧ xshape x lb

theorem rowShXMap (k : Nat) (row : List Lbl) (sh : List Ritem) :
    RowShX k row (sh.map .it) ↔ RowSh k row sh := by
  constructor
  · intro H j it Hj
    exact H j (.it it) (by rw [List.getElem?_map, Hj]; rfl)
  · intro H j x Hj
    rw [List.getElem?_map] at Hj
    cases h : sh[j]? with
    | none => rw [h] at Hj; cases Hj
    | some it =>
      rw [h] at Hj; cases Hj
      exact H j it h

theorem rowShXAppL (k : Nat) (row : List Lbl) (s1 s2 : List Rxitem) :
    RowShX k row (s1 ++ s2) → RowShX k row s1 :=
  fun H j x Hj => H j x (lookup_app_l_Some Hj)

theorem rowShXAppR (k : Nat) (row : List Lbl) (s1 s2 : List Rxitem) :
    RowShX k row (s1 ++ s2) → RowShX (k + s1.length) row s2 := by
  intro H j x Hj
  obtain ⟨lb, Hlb, Hs⟩ := H (s1.length + j) x (by
    rw [List.getElem?_append_right (by omega), show s1.length + j - s1.length = j by omega]
    exact Hj)
  exact ⟨lb, by rw [show k + s1.length + j = k + (s1.length + j) by omega]; exact Hlb, Hs⟩

theorem rowShXLen (k : Nat) (row : List Lbl) (sh : List Rxitem) :
    RowShX k row sh → sh ≠ [] → k + sh.length ≤ row.length := by
  intro H Hne
  have Hl : 0 < sh.length := List.length_pos_iff.2 Hne
  obtain ⟨lb, Hlb, _⟩ := H (sh.length - 1) _ (List.getElem?_eq_getElem (by omega))
  have := (List.getElem?_eq_some_iff.1 Hlb).1
  omega

/-- `itDisj` for `Rxitem`: a write item misses `[pa, pa + w)`. -/
def xitDisj (pa : Int) (w : Nat) (x : Rxitem) : Prop :=
  match x with
  | .it i => itDisj pa w i
  | .RB .. => True
  | .RSc pb m _ => dj pb m pa w
  | .RM _ _ pb m => dj pb m pa w

/-- NO-WRITE-BETWEEN from a matched window (as AxSpinPOr's `rowShNowr`). -/
theorem rowShXNowr (k : Nat) (row : List Lbl) (sh : List Rxitem) (jw jr : Nat) (pa : Int)
    (w : Nat) :
    RowShX k row sh → jr ≤ sh.length →
    (∀ x ∈ (sh.take jr).drop (jw + 1), xitDisj pa w x) →
    nowr row (k + jw) (k + jr) pa w := by
  intro H Hle HF k' lb rl b m Hk Hlb Hid
  obtain ⟨x, Hx⟩ : ∃ x, sh[k' - k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨lb', Hlb', Hs⟩ := H (k' - k) x Hx
  rw [show k + (k' - k) = k' by omega, Hlb] at Hlb'
  cases Hlb'
  have Hj : ((sh.take jr).drop (jw + 1))[k' - k - (jw + 1)]? = some x := by
    rw [List.getElem?_drop, List.getElem?_take, if_pos (by omega),
      show jw + 1 + (k' - k - (jw + 1)) = k' - k by omega]
    exact Hx
  have Hd : xitDisj pa w x := HF x (List.mem_of_getElem? Hj)
  cases x with
  | it i =>
    cases i with
    | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hid; cases Hid
    | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid
    | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid
    | RS pb n =>
      obtain ⟨vw, cls, rfl, Hl⟩ := Hs
      simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
      obtain ⟨_, rfl, rfl⟩ := Hid
      rw [Hl]; exact Hd
  | RB pr pw sr sw => rw [Hs] at Hid; cases Hid
  | RSc pb n cls =>
    obtain ⟨vw, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    rw [Hl]; exact Hd
  | RM aq rl' pb n =>
    rw [Hs] at Hid
    simp only [aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    exact Hd

/-- A fence item's label. -/
theorem xshapeRB (pr pw sr sw : Bool) (lb : Lbl) :
    xshape (.RB pr pw sr sw) lb → lb = .LFence pr pw sr sw := by
  intro H
  cases lb <;> simp only [xshape, aident, reduceCtorEq] at H
  simp only [AidentT.IFence.injEq] at H
  obtain ⟨rfl, rfl, rfl, rfl⟩ := H
  rfl

/-- A replicated RMW window is AxSpinAqr's `RowSpin` (T2a's spin items). -/
theorem rowSpinOfX (u n : Nat) (row : List Lbl) (plk : Int) :
    RowShX u row (List.replicate (n + 1) (.RM true false plk 4)) → RowSpin u n row plk := by
  intro H j Hj
  exact H j _ (List.getElem?_replicate_of_lt (by omega))

/-! # 2. holding's window as a list -/

/-- holding's window: the lw of `lk->locked`, and on the long path (`hb`) the three spills, the
`lk->cpu` read, mycpu's window and the three reloads (AxSpinHd8 §1 positions). -/
def holdShB (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) : List Ritem :=
  if hb then
    [.RL plk 4, .RS pra 8, .RS ps0 8, .RS ps1 8, .RL pcl 8] ++ mycSh pram ps0m ++
      [.RL pra 8, .RL ps0 8, .RL ps1 8]
  else [.RL plk 4]

/-- holding's window length (= its continuation offset). -/
def holdLen (hb : Bool) : Nat := if hb then 12 else 1

theorem holdShBLen (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    (holdShB hb plk pcl pra ps0 ps1 pram ps0m).length = holdLen hb := by
  cases hb <;> rfl

/-- Plan ID-1 `Row_holding_of`. -/
theorem rowHoldingOf (k : Nat) (row : List Lbl) (hb : Bool) (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowSh k row (holdShB hb plk pcl pra ps0 ps1 pram ps0m) → lkBranch row k hb →
    k + holdLen hb < row.length → RowHolding k row hb plk pcl pra ps0 ps1 pram ps0m := by
  intro H Hb Hlen
  refine ⟨Hb, ?_⟩
  cases hb with
  | false =>
    refine ⟨Hlen, fun j Hj => ?_⟩
    match j, Hj with
    | 0, _ => exact H 0 _ rfl
  | true =>
    refine ⟨Hlen, fun j Hj Hr => ?_, ?_⟩
    · match j, Hj, Hr with
      | 0, _, _ => exact H 0 _ rfl
      | 1, _, _ => exact H 1 _ rfl
      | 2, _, _ => exact H 2 _ rfl
      | 3, _, _ => exact H 3 _ rfl
      | 4, _, _ => exact H 4 _ rfl
      | 9, _, _ => exact H 9 _ rfl
      | 10, _, _ => exact H 10 _ rfl
      | 11, _, _ => exact H 11 _ rfl
      | 5, _, Hr | 6, _, Hr | 7, _, Hr | 8, _, Hr => omega
    · apply rowMycpuOf
      · intro j it Hj
        obtain ⟨lb, Hlb, Hs⟩ := H (5 + j) it (by
          simp only [holdShB, ↓reduceIte]
          rw [List.getElem?_append_left (by
              have := (List.getElem?_eq_some_iff.1 Hj).1
              simp only [mycLen] at this; simp only [List.length_append, mycLen,
                List.length_cons, List.length_nil]; omega),
            List.getElem?_append_right (by simp)]
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
          exact Hj)
        exact ⟨lb, by rw [show k + 5 + j = k + (5 + j) by omega]; exact Hlb, Hs⟩
      · simp only [holdLen, ↓reduceIte] at Hlen; omega

/-! # 3. release's window and its positions -/

/-- release + 0x02 … 0x06: the three spills. -/
def relHead (pra ps0 ps1 : Int) : List Ritem := [.RS pra 8, .RS ps0 8, .RS ps1 8]
/-- release + 0x22 … 0x26: the three reloads. -/
def relTail (pra ps0 ps1 : Int) : List Ritem := [.RL pra 8, .RL ps0 8, .RL ps1 8]
/-- pop_off's window length (AxSpinPO6: `ppSh c` has 10 / 11 items). -/
def ppLen (c : Bool) : Nat := 10 + (if c then 0 else 1)

theorem ppShLen (c : Bool) (pra ps0 pmra pms0 pn pint : Int) :
    (ppSh c pra ps0 pmra pms0 pn pint).length = ppLen c := by
  cases c <;> rfl

/-- THE RELEASE WINDOW.  Slots: release's `pra ps0 ps1`; the lock word `plk`, `lk->cpu` `pcl`;
holding's slots `hra hs0 hs1` and its mycpu's `hram hs0m`; pop_off's slots `qra qs0`, its mycpu's
`qmra qms0`, the cpu fields `pn` (noff) / `pint` (intena); `c` = pop_off's arm. -/
def relSh (c : Bool) (pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int) :
    List Rxitem :=
  (relHead pra ps0 ps1).map .it ++ ((holdShB true plk pcl hra hs0 hs1 hram hs0m).map .it ++
    ([.it (.RS pcl 8), .RB true true false true, .RSc plk 4 .WCrel] ++
      ((ppSh c qra qs0 qmra qms0 pn pint).map .it ++ (relTail pra ps0 ps1).map .it)))

/-- holding's first event. -/
def relKh (k : Nat) : Nat := k + 3
/-- `sd zero,16(s1)`. -/
def relKc (k : Nat) : Nat := k + 15
/-- `fence rw,w`. -/
def relKf (k : Nat) : Nat := k + 16
/-- `sw zero,0(s1)` (the releasing store). -/
def relKw (k : Nat) : Nat := k + 17
/-- pop_off's first event. -/
def relKp (k : Nat) : Nat := k + 18
/-- the first reload (= pop_off's continuation boundary). -/
def relKr (k : Nat) (c : Bool) : Nat := relKp k + ppLen c
/-- the boundary after release's c.ret. -/
def relKe (k : Nat) (c : Bool) : Nat := relKr k c + 3
/-- the window length. -/
def relLen (c : Bool) : Nat := 21 + ppLen c

theorem relShLen (c : Bool) (pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn
    pint : Int) :
    (relSh c pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint).length =
      relLen c := by
  cases c <;> rfl

theorem relKeEq (k : Nat) (c : Bool) : relKe k c = k + relLen c := by
  simp only [relKe, relKr, relKp, relLen]; omega

/-- THE ROW OF release at `k` (pop_off arm `c`): the window, holding's long path (the lock is
held), and a row item after the c.ret's boundary. -/
def RowRelease (k : Nat) (c : Bool) (row : List Lbl)
    (pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int) : Prop :=
  RowShX k row (relSh c pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint) ∧
  lkBranch row (relKh k) true ∧ relKe k c < row.length

/-- Position congruence for `RowSh`. -/
theorem AxSpinRl1.rowShCongr {k k' : Nat} {row : List Lbl} {sh : List Ritem} :
    RowSh k row sh → k = k' → RowSh k' row sh := fun H e => e ▸ H

section rowrel
variable {k : Nat} {c : Bool} {row : List Lbl}
  {pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int}

theorem rowReleaseHead :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowSh k row (relHead pra ps0 ps1) := fun H =>
  (rowShXMap _ _ _).1 (rowShXAppL _ _ _ _ H.1)

theorem rowReleaseHolding :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowHolding (relKh k) row true plk pcl hra hs0 hs1 hram hs0m := by
  intro H
  have H1 := (rowShXMap _ _ _).1 (rowShXAppL _ _ _ _ (rowShXAppR _ _ _ _ H.1))
  refine rowHoldingOf _ _ true _ _ _ _ _ _ _ H1 H.2.1 ?_
  have := H.2.2
  simp only [relKe, relKr, relKp, relKh, holdLen, ↓reduceIte] at this ⊢; omega

theorem rowReleaseItem (j : Nat) (x : Rxitem) :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    (relSh c pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint)[j]? = some x →
    ∃ lb, row[k + j]? = some lb ∧ xshape x lb := fun H => H.1 j x

theorem rowReleaseCpu :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    ∃ vw cls, row[relKc k]? = some (.LStore false pcl vw cls) ∧ vw.length = 8 := by
  intro H
  obtain ⟨lb, Hlb, vw, cls, rfl, Hl⟩ := rowReleaseItem 15 (.it (.RS pcl 8)) H (by cases c <;> rfl)
  exact ⟨vw, cls, Hlb, Hl⟩

theorem rowReleaseFence :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    row[relKf k]? = some (.LFence true true false true) := by
  intro H
  obtain ⟨lb, Hlb, Hs⟩ := rowReleaseItem 16 (.RB true true false true) H (by cases c <;> rfl)
  rw [xshapeRB _ _ _ _ _ Hs] at Hlb
  exact Hlb

theorem rowReleaseRel :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    ∃ vw, row[relKw k]? = some (.LStore false plk vw .WCrel) ∧ vw.length = 4 := by
  intro H
  obtain ⟨lb, Hlb, vw, rfl, Hl⟩ := rowReleaseItem 17 (.RSc plk 4 .WCrel) H (by cases c <;> rfl)
  exact ⟨vw, Hlb, Hl⟩

theorem rowReleasePop :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowSh (relKp k) row (ppSh c qra qs0 qmra qms0 pn pint) := by
  intro H
  have H1 := (rowShXMap _ _ _).1 (rowShXAppL _ _ _ _ (rowShXAppR _ _ _ _ (rowShXAppR _ _ _ _
    (rowShXAppR _ _ _ _ H.1))))
  exact AxSpinRl1.rowShCongr H1 (by
    simp only [List.length_map, List.length_cons, List.length_nil, List.length_append, relHead,
      holdShB, ↓reduceIte, mycLen, relKp])

theorem rowReleaseTail :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowSh (relKr k c) row (relTail pra ps0 ps1) := by
  intro H
  have H1 := (rowShXMap _ _ _).1 (rowShXAppR _ _ _ _ (rowShXAppR _ _ _ _ (rowShXAppR _ _ _ _
    (rowShXAppR _ _ _ _ H.1))))
  exact AxSpinRl1.rowShCongr H1 (by
    simp only [List.length_map, List.length_cons, List.length_nil, List.length_append, relHead,
      holdShB, ↓reduceIte, mycLen, ppShLen, relKr, relKp])

/-- The continuation boundary after the c.ret has a next row item (`XxRet`'s `k < LEN`); pop_off's
continuation (`tk + 2 < row.length` of `wpdPopOff`) and the tail's are below it. -/
theorem rowReleaseLen :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    relKe k c < row.length ∧ relKr k c + 2 < row.length := by
  intro H
  have := H.2.2
  exact ⟨this, by simp only [relKe] at this; omega⟩

/-- The writes of the window strictly between the spills and the reloads (positions k+3 …
relKr − 1): holding's five spills, `lk->cpu`, the lock word, pop_off's five stores. -/
def relWr (plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn : Int) : List (Int × Nat) :=
  [(hra, 8), (hs0, 8), (hs1, 8), (hram, 8), (hs0m, 8), (pcl, 8), (plk, 4),
    (qra, 8), (qs0, 8), (qmra, 8), (qms0, 8), (pn, 4)]

/-- NO-WRITE-BETWEEN for spill `s` (ra / s0 / s1) and its reload at `relKr k c + s`: the slot
misses the later spills and every `relWr` write. -/
theorem rowReleaseNowr (s : Nat) (hs : s < 3) (pa : Int) (w : Nat) :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    (∀ q ∈ ([(pra, 8), (ps0, 8), (ps1, 8)] : List (Int × Nat)).drop (s + 1), dj q.1 q.2 pa w) →
    (∀ q ∈ relWr plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn, dj q.1 q.2 pa w) →
    nowr row (k + s) (relKr k c + s) pa w := by
  intro H Hs Hd
  rw [show relKr k c + s = k + (18 + ppLen c + s) by simp only [relKr, relKp]; omega]
  refine rowShXNowr k row _ s _ pa w H.1 (by rw [relShLen]; simp only [relLen]; omega) ?_
  simp only [relWr, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    at Hd
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ := Hd
  match s, hs with
  | 0, _ =>
    simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at Hs
    obtain ⟨e1, e2⟩ := Hs
    cases c <;>
    simp only [relSh, relHead, holdShB, mycSh, ppSh, ppHead, ppMid, ppTail, relTail, ppLen,
      ↓reduceIte, Bool.false_eq_true, List.map, List.cons_append, List.nil_append,
      Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, xitDisj, itDisj,
      true_and, and_true] <;>
    exact ⟨e1, e2, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
  | 1, _ =>
    simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq] at Hs
    cases c <;>
    simp only [relSh, relHead, holdShB, mycSh, ppSh, ppHead, ppMid, ppTail, relTail, ppLen,
      ↓reduceIte, Bool.false_eq_true, List.map, List.cons_append, List.nil_append,
      Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, xitDisj, itDisj,
      true_and, and_true] <;>
    exact ⟨Hs, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
  | 2, _ =>
    cases c <;>
    simp only [relSh, relHead, holdShB, mycSh, ppSh, ppHead, ppMid, ppTail, relTail, ppLen,
      ↓reduceIte, Bool.false_eq_true, List.map, List.cons_append, List.nil_append,
      Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, xitDisj, itDisj,
      true_and, and_true] <;>
    exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩

end rowrel

/-! # 4. Honesty of the pinned class (ID-6) -/

/-- The release-pending flag along ROW labels (`AxClsStep.relpUpd` on the memory labels). -/
def relpLb (lb : Lbl) (r : Bool) : Bool :=
  match lb with
  | .LFence _ pw _ sw => if (pw && sw) then true else r
  | .LStore .. | .LRmw .. => false
  | .LLoad .. => r
  | .LIo .. => r

/-- The flag just before row item `k`. -/
def relpAt (row : List Lbl) (k : Nat) : Bool :=
  (row.take k).foldl (fun r lb => relpLb lb r) false

theorem relpAtZero (row : List Lbl) : relpAt row 0 = false := by
  simp [relpAt]

theorem relpAtSucc (row : List Lbl) (k : Nat) (lb : Lbl) :
    row[k]? = some lb → relpAt row (k + 1) = relpLb lb (relpAt row k) := by
  intro h
  simp only [relpAt, List.take_add_one, h, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- The class `wmClassOf` stamps on a row label, given the flag (`true` = nothing to check). -/
def lbClsOk (r : Bool) (lb : Lbl) : Bool :=
  match lb with
  | .LStore rl _ _ cls => decide (cls = if (rl || r) then .WCrel else .WCplain)
  | .LRmw _ _ _ _ _ _ cls => decide (cls = .WCexcl)
  | _ => true

/-- ID-6 `row_cls_honest`: every store's class is the one the language stamps. -/
def rowClsHonest (row : List Lbl) : Prop :=
  ∀ k lb, row[k]? = some lb →
    (∀ rl pa vw cls, lb = .LStore rl pa vw cls →
      cls = if (rl || relpAt row k) then .WCrel else .WCplain) ∧
    (∀ aq rl pa ts rvs wvs cls, lb = .LRmw aq rl pa ts rvs wvs cls → cls = .WCexcl)

/-- The Bool checker (certificates: `decide +kernel` on a literal row). -/
def AxSpinRl1.clsGo : Bool → List Lbl → Bool
  | _, [] => true
  | r, lb :: l => lbClsOk r lb && AxSpinRl1.clsGo (relpLb lb r) l

def rowClsOkB (row : List Lbl) : Bool := AxSpinRl1.clsGo false row

theorem AxSpinRl1.clsGoSound (row : List Lbl) (r : Bool) :
    AxSpinRl1.clsGo r row = true → ∀ k lb, row[k]? = some lb →
      lbClsOk ((row.take k).foldl (fun r lb => relpLb lb r) r) lb = true := by
  induction row generalizing r with
  | nil => intro _ k lb h; simp at h
  | cons x l ih =>
    intro H k lb h
    simp only [AxSpinRl1.clsGo, Bool.and_eq_true] at H
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simpa using H.1
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.take_succ_cons, List.foldl_cons]
      exact ih _ H.2 k lb h

theorem rowClsHonestOfB (row : List Lbl) : rowClsOkB row = true → rowClsHonest row := by
  intro H k lb h
  have Hk := AxSpinRl1.clsGoSound row false H k lb h
  change lbClsOk (relpAt row k) lb = true at Hk
  constructor
  · intro rl pa vw cls e
    subst e
    exact of_decide_eq_true Hk
  · intro aq rl pa ts rvs wvs cls e
    subst e
    exact of_decide_eq_true Hk

section rowrelp
variable {k : Nat} {c : Bool} {row : List Lbl}
  {pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int}

/-- The `fence rw,w` at `relKf` arms the flag for the releasing store. -/
theorem rowReleaseRelp :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    relpAt row (relKw k) = true := by
  intro H
  rw [show relKw k = relKf k + 1 from rfl, relpAtSucc row _ _ (rowReleaseFence H)]
  rfl

/-- The releasing store's pinned `WCrel` is the honest class. -/
theorem rowReleaseRelHonest :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    WmClass.WCrel = if (false || relpAt row (relKw k)) then .WCrel else .WCplain := by
  intro H
  rw [rowReleaseRelp H]
  rfl

/-- The releasing store clears the flag (pop_off's stores are plain under `rowClsHonest`). -/
theorem rowReleaseRelpClear :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    relpAt row (relKw k + 1) = false := by
  intro H
  obtain ⟨vw, Hw, -⟩ := rowReleaseRel H
  rw [relpAtSucc row _ _ Hw]
  rfl

end rowrelp

end Weak
