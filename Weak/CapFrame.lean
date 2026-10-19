/-
Weak: **W11-F row 6g — A9 `FrameWin` at the route-P `SbCand` member: THE GLUE** (plan rev 56 row 6g,
"as 6a"; interface `PinTrapFrame.FrameWin`, `Weak/PinTrapFrame.lean:268`).  Lean-only, no Rocq twin.

`PinTrapFrame.FrameWin G σ j pa s w k` asks, at the restore `(j, k)`'s post-state `σ`, for the spill
`(j, w)` at write index `s`: (`acqIn`) a hop-acquire entry of `j` after `s` is an `.aq` event po-between
the two; (`pubIn`) `j`'s observation of a publication store after `s` is a read of a publication byte
po-between; (`ownIn`) an own write to `pa` after `s` is po-between.

  §1  **THE WALK'S ROW ORDER, the store side** (PROVED, P-W2 level — `CapSync.rowOrdStAt`'s companion):
      along a valid walk, a gmo entry `y` is preceded in gmo by every po-earlier AT-EVENT event of its row
      (a load / AMO is in gmo at its event, before a po-later store is even issued) and by every po-earlier
      own plain store writing a common byte (riscv.cat rule 1 as [OWN.113]'s per-address buffer,
      `SbPol.sameAddr`) — `CapFrame.beforeStAt`; the tagged buffers are sorted by row index
      (`CapFrame.pendSortedStAt`).
  §2  the member form (`CapFrame.memberEvBefore`, `CapFrame.memberStBefore`).
  §3  **the realization interface** (NAMED, P-W6's step map, 6a's `floorReadReal` with the byte):
      `CapFrame.floorByteReal` — `j`'s floor at a publication byte naming a store at `r` was raised by a
      realized READ OF THAT BYTE by `j` (issuing pc `ipc Y` = the ghost record's `lr j f` [OWN.119]) of a
      write at or after `r`, at or before the restore (MachCSL raises `coh j f` only at `j`'s own loads of
      `f`: `HRead.afterLoad`, `MachCSL/TsoMem.lean:358`; stores reset it, AMOs keep it).
  §4  **THE GLUE** `CapFrame.frameWinOf` — `FrameWin` at the member from 6a's interim premises
      (`CapSync.lockNzExclP` [OWN.118], `CapSync.startedFloorPcP` [OWN.119]), 6a's interfaces
      (`CapSync.exclHopReal`, `CapSync.realBefore` at the restore), GF's `.aq` image fact
      (`CapSync.amoAqAt`), §1–§3, and the restore's SITE fact `ipc (j, k) ≠ main+0x16` (census:
      `PinTrapFrame.frameHoldEnds` puts the restore pcs in `frameWinPcs`, `frameWindowsNoStarted`);
      plus the SITE-level publication arm `CapFrame.pubInSite` / `CapFrame.k2OfSite`: the window's
      publication read is at `main+0x16`, so the decided site census `frameWindowsNoStarted` (no
      `started`-load site in any window) refutes `pubSeenAfter` without `FrameQuiet.noPub`'s
      address reading (the deviation in `PinTrapFrame`'s header).

Spec: riscv.cat rule 1 (`[M];po-loc;[W]`) is the per-address buffer's law; RVWMO's load-value axiom and
gmo are the member's; the premises are xv6 run facts (FAITHFUL once discharged, WEAKER while named —
the same two as 6a, queued Q2/Q4).  Names `CapFrame.*`.
-/
import Weak.CapSync
import Weak.PinTrapFrame

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CapFrame

open SbWalk SbAgree

/-! # 1. The walk's row order, the store side -/

/-- `x` and `y` are plain stores of the walk writing a common byte. -/
def stPair (w : WS) (x y : Geid) : Prop :=
  ∃ (r1 : Bool) (b1 : Int) (v1 : List (BitVec 8)) (k1 : WmClass) (r2 : Bool) (b2 : Int)
    (v2 : List (BitVec 8)) (k2 : WmClass) (j1 j2 : Nat),
    (w.rows x.1)[x.2]? = some (LStore r1 b1 v1 k1) ∧ (w.rows y.1)[y.2]? = some (LStore r2 b2 v2 k2) ∧
    j1 < v1.length ∧ j2 < v2.length ∧ accAddr b1 j1 = accAddr b2 j2

/-- **THE STORE-SIDE ROW ORDER**: every gmo entry `y` is preceded in gmo by each po-earlier at-event
event of its row and by each po-earlier own plain store sharing a byte with it. -/
def Before (w : WS) : Prop :=
  ∀ (b : Nat) (y x : Geid), w.gmo[b]? = some y → x.1 = y.1 → x.2 < y.2 →
    (CapSync.evAt w x ∨ stPair w x y) → ∃ a, a < b ∧ w.gmo[a]? = some x

/-- The tagged buffers are sorted by row index. -/
def PendSorted (w : WS) : Prop := ∀ i, ((w.pend i).map Prod.fst).Pairwise (· < ·)

theorem pendSortedInit (img : Image) : PendSorted (init img) := fun _ => List.Pairwise.nil

theorem pendSortedEv (img : Image) (w : WS) (s : Estep) :
    Inv img w → PendSorted w → PendSorted (nextI w (.ev s)) := by
  intro hI hS i
  show ((upd w.pend s.esAg (pendE w s.esAg s.esLb) i).map Prod.fst).Pairwise _
  by_cases hi : i = s.esAg
  · subst hi
    rw [updEq]
    unfold pendE
    split
    · rw [List.map_append, List.pairwise_append]
      refine ⟨hS _, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      obtain ⟨rl, base, vs, kc, hl, -⟩ := hI.pendSt _ p hp
      exact (List.getElem?_eq_some_iff.1 hl).1
    · split
      · rw [List.map_map]
        have : (Prod.fst ∘ fun p : Nat × SbEnt => (p.1, p.2.bump)) = Prod.fst := rfl
        rw [this]; exact hS _
      · exact hS _
    · exact hS _
  · rw [updNe _ _ _ _ hi]; exact hS i

theorem pendSortedLand (w : WS) (i k : Nat) : PendSorted w → PendSorted (nextI w (.land i k)) := by
  intro hS j
  cases hp : (w.pend i)[k]? with
  | none => simp only [nextI, hp]; exact hS j
  | some p =>
    simp only [nextI, hp]
    show ((upd w.pend i ((w.pend i).eraseIdx k) j).map Prod.fst).Pairwise _
    by_cases hj : j = i
    · subst hj; rw [updEq]
      exact (hS j).sublist ((List.eraseIdx_sublist _ _).map _)
    · rw [updNe _ _ _ _ hj]; exact hS j

theorem pendSortedStAt (pol : SbPol) (c : CandW) (hv : validW pol c) : ∀ k, PendSorted (stAt c k) := by
  intro k
  induction k with
  | zero => exact pendSortedInit c.img
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      show PendSorted (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k)
      rw [hk]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      cases it with
      | ev s => exact pendSortedEv c.img _ s (invStAt pol c hv k) ih
      | land i j => exact pendSortedLand _ i j ih

/-- A pending entry's row label is a plain store, so it is not at-event. -/
theorem pendNotEv (img : Image) (w : WS) (hI : Inv img w) (i : Nat) (p : Nat × SbEnt)
    (hp : p ∈ w.pend i) : ¬ CapSync.evAt w (i, p.1) := by
  rintro ⟨l, hl, hg⟩
  obtain ⟨rl, base, vs, kc, hl', -⟩ := hI.pendSt i p hp
  change (w.rows i)[p.1]? = some l at hl
  rw [hl'] at hl
  cases hl
  simp [gmoEv, isSt] at hg

/-- A row memory event that is not pending is in gmo. -/
theorem memOfNotPend (img : Image) (w : WS) (hI : Inv img w) (x : Geid) (l : Lbl)
    (hl : (w.rows x.1)[x.2]? = some l) (hm : lbIsMem l = true) :
    x ∈ w.gmo ∨ ∃ p, p ∈ w.pend x.1 ∧ p.1 = x.2 := by
  rcases hI.memIn x.1 x.2 l hl hm with h | h
  · exact .inl h
  · obtain ⟨p, hp, he⟩ := List.mem_map.1 h
    exact .inr ⟨p, hp, he⟩

theorem lookupOfMem {α : Type} {l : List α} {a : α} (h : a ∈ l) : ∃ n, n < l.length ∧ l[n]? = some a := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 h
  exact ⟨n, (List.getElem?_eq_some_iff.1 hn).1, hn⟩

theorem beforeInit (img : Image) : Before (init img) := by
  intro b y x hy
  simp [init] at hy

theorem stPairEv (w : WS) (s : Estep) (x y : Geid) (hx : x.2 < (w.rows x.1).length)
    (hy : y.2 < (w.rows y.1).length) : stPair (nextI w (.ev s)) x y ↔ stPair w x y := by
  unfold stPair
  rw [CapSync.rowsEvGet w s x hx, CapSync.rowsEvGet w s y hy]

theorem beforeEv (img : Image) (w : WS) (s : Estep) :
    Inv img w → Before w → Before (nextI w (.ev s)) := by
  intro hI hB b y x hy hxy hlt hc
  have hgmo : (nextI w (.ev s)).gmo =
      if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo := rfl
  -- an OLD gmo entry: its row is unchanged below it
  have hold : ∀ y, w.gmo[b]? = some y → x.1 = y.1 → x.2 < y.2 →
      (CapSync.evAt (nextI w (.ev s)) x ∨ stPair (nextI w (.ev s)) x y) →
      ∃ a, a < b ∧ (nextI w (.ev s)).gmo[a]? = some x := by
    intro y hy hxy hlt hc
    have hyl : y.2 < (w.rows y.1).length := by
      obtain ⟨l, hl, -⟩ := hI.gmoMem y (List.mem_of_getElem? hy)
      exact (List.getElem?_eq_some_iff.1 hl).1
    have hxl : x.2 < (w.rows x.1).length := by rw [hxy]; omega
    have hc' : CapSync.evAt w x ∨ stPair w x y := by
      rcases hc with h | h
      · exact .inl ((CapSync.evAtEv w s x hxl).1 h)
      · exact .inr ((stPairEv w s x y hxl hyl).1 h)
    obtain ⟨a, hab, ha⟩ := hB b y x hy hxy hlt hc'
    have hbl : b < w.gmo.length := (List.getElem?_eq_some_iff.1 hy).1
    refine ⟨a, hab, ?_⟩
    rw [hgmo]
    split
    · rw [List.getElem?_append_left (by omega)]; exact ha
    · exact ha
  rw [hgmo] at hy
  split at hy
  · rename_i hev
    by_cases hb : b < w.gmo.length
    · rw [List.getElem?_append_left hb] at hy
      exact hold y hy hxy hlt hc
    · have hb' : b = w.gmo.length := by
        have := (List.getElem?_eq_some_iff.1 hy).1
        simp only [List.length_append, List.length_singleton] at this
        omega
      subst hb'
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      simp only at hxy hlt
      have hxl : x.2 < (w.rows x.1).length := by rw [hxy]; exact hlt
      -- the new entry is at-event, so not a plain store: only the at-event arm
      have hev' : CapSync.evAt w x := by
        rcases hc with h | ⟨r1, b1, v1, k1, r2, b2, v2, k2, j1, j2, -, h2, -⟩
        · exact (CapSync.evAtEv w s x hxl).1 h
        · exfalso
          have hr : ((nextI w (.ev s)).rows s.esAg)[(w.rows s.esAg).length]? = some s.esLb := by
            show (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) s.esAg)[_]? = _
            rw [updEq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
          simp only at h2
          rw [hr, Option.some.injEq] at h2
          rw [h2] at hev
          simp [gmoEv, isSt] at hev
      obtain ⟨l, hl, hg⟩ := hev'
      rcases memOfNotPend img w hI x l hl (by
          unfold gmoEv at hg; simp only [Bool.and_eq_true] at hg; exact hg.1) with hm | ⟨p, hp, hpx⟩
      · obtain ⟨a, ha, hax⟩ := lookupOfMem hm
        exact ⟨a, ha, by rw [hgmo, if_pos hev, List.getElem?_append_left ha]; exact hax⟩
      · exfalso
        have := pendNotEv img w hI x.1 p hp
        rw [hpx] at this
        exact this ⟨l, hl, hg⟩
  · exact hold y hy hxy hlt hc

theorem beforeLand (img : Image) (pol : SbPol) (w : WS) (i k : Nat) :
    Inv img w → PendSorted w → pol.landOk (w.σ.sb i) k → Before w → Before (nextI w (.land i k)) := by
  intro hI hS hok hB
  cases hpk : (w.pend i)[k]? with
  | none => simp only [nextI, hpk]; exact hB
  | some p =>
    have heq : nextI w (.land i k) =
        ⟨SbCand.nextL w.σ i k, upd w.pend i ((w.pend i).eraseIdx k), w.rows, w.fw,
          w.gmo ++ [(i, p.1)]⟩ := by
      simp only [nextI, hpk]
    rw [heq]
    intro b y x hy hxy hlt hc
    change CapSync.evAt w x ∨ stPair w x y at hc
    change (w.gmo ++ [(i, p.1)])[b]? = some y at hy
    change ∃ a, a < b ∧ (w.gmo ++ [(i, p.1)])[a]? = some x
    by_cases hb : b < w.gmo.length
    · rw [List.getElem?_append_left hb] at hy
      obtain ⟨a, hab, ha⟩ := hB b y x hy hxy hlt hc
      exact ⟨a, hab, by rw [List.getElem?_append_left (by omega)]; exact ha⟩
    · have hb' : b = w.gmo.length := by
        have := (List.getElem?_eq_some_iff.1 hy).1
        simp only [List.length_append, List.length_singleton] at this
        omega
      subst hb'
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      simp only at hxy hlt
      have hpm : p ∈ w.pend i := List.mem_of_getElem? hpk
      -- the landed entry's row label and message
      obtain ⟨rlp, bp, vp, kp, hlp, hmp⟩ := hI.pendSt i p hpm
      have fin : x ∈ w.gmo → ∃ a, a < w.gmo.length ∧ (w.gmo ++ [(i, p.1)])[a]? = some x := by
        intro hm
        obtain ⟨a, ha, hax⟩ := lookupOfMem hm
        exact ⟨a, ha, by rw [List.getElem?_append_left ha]; exact hax⟩
      rcases hc with ⟨l, hl, hg⟩ | ⟨r1, b1, v1, k1, r2, b2, v2, k2, j1, j2, h1, h2, hj1, hj2, hab⟩
      · rcases memOfNotPend img w hI x l hl (by
            unfold gmoEv at hg; simp only [Bool.and_eq_true] at hg; exact hg.1) with hm | ⟨q, hq, hqx⟩
        · exact fin hm
        · exfalso
          have := pendNotEv img w hI x.1 q hq
          rw [hqx] at this
          exact this ⟨l, hl, hg⟩
      · rcases memOfNotPend img w hI x _ h1 rfl with hm | ⟨q, hq, hqx⟩
        · exact fin hm
        · exfalso
          rw [hxy] at hq
          obtain ⟨k', hk', hqk⟩ := lookupOfMem hq
          -- sorted tags: the older entry is at a smaller index
          have hkk : k' < k := by
            have hsrt := hS i
            have hk1 : ((w.pend i).map Prod.fst)[k']? = some q.1 := by
              rw [List.getElem?_map, hqk]; rfl
            have hk2 : ((w.pend i).map Prod.fst)[k]? = some p.1 := by
              rw [List.getElem?_map, hpk]; rfl
            rcases Nat.lt_trichotomy k' k with h | h | h
            · exact h
            · subst h; rw [hqk, Option.some.injEq] at hpk; subst hpk; omega
            · have := CapSync.pairLookup _ k k' p.1 q.1 hsrt hk2 hk1 h
              omega
          obtain ⟨rlq, bq, vq, kq, hlq, hmq⟩ := hI.pendSt i q hq
          -- the two rows' labels are the pair's
          have e1 : (w.rows i)[q.1]? = some (LStore r1 b1 v1 k1) := by
            rw [hqx]; rw [hxy] at h1; exact h1
          rw [hlq, Option.some.injEq] at e1
          cases e1
          simp only at h2
          rw [hlp, Option.some.injEq] at h2
          cases h2
          have hsb := hI.sb i
          have hq' : (w.σ.sb i)[k']? = some q.2 := by rw [hsb, List.getElem?_map, hqk]; rfl
          have hp' : (w.σ.sb i)[k]? = some p.2 := by rw [hsb, List.getElem?_map, hpk]; rfl
          apply pol.sameAddr _ k k' p.2 q.2 hok hkk hq' hp'
          refine ⟨j2, by rw [hmp]; exact hj2, ?_⟩
          rw [hmp, hmq]
          simp only
          rw [← hab]
          exact msgByteInRange _ _ _ _ j1 hj1

theorem beforeStAt (pol : SbPol) (c : CandW) (hv : validW pol c) : ∀ k, Before (stAt c k) := by
  intro k
  induction k with
  | zero => exact beforeInit c.img
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      show Before (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k)
      rw [hk]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      have hI := invStAt pol c hv k
      cases it with
      | ev s => exact beforeEv c.img _ s hI ih
      | land i j => exact beforeLand c.img pol _ i j hI (pendSortedStAt pol c hv k) (hv k _ hk) ih

/-! # 2. The member form -/

theorem memberGmo (N : Nat) (c : CandW) : (memberP N c).gxGmo = (cur c).gmo := rfl

theorem memberNodup (pol : SbPol) (N : Nat) (c : CandW) (hv : validW pol c) :
    (memberP N c).gxGmo.Nodup := (invStAt pol c hv c.its.length).gmoNd

/-- Lookups to positions in the member's gmo. -/
theorem gmoLtOfIdx (pol : SbPol) (N : Nat) (c : CandW) (hv : validW pol c) (x y : Geid) (a b : Nat)
    (hx : (cur c).gmo[a]? = some x) (hy : (cur c).gmo[b]? = some y) (hab : a < b) :
    gmoLt (memberP N c) x y := by
  have hnd := memberNodup pol N c hv
  refine ⟨List.mem_of_getElem? hx, List.mem_of_getElem? hy, ?_⟩
  rw [gposOfLookup _ a x hnd hx, gposOfLookup _ b y hnd hy]
  exact hab

/-- **A po-earlier at-event event of the row is gmo-before** any member gmo entry. -/
theorem memberEvBefore (pol : SbPol) (N : Nat) (c : CandW) (hv : validW pol c) (x y : Geid) (lx : Lbl)
    (hy : y ∈ (memberP N c).gxGmo) (hxy : x.1 = y.1) (hlt : x.2 < y.2)
    (hx : gxLbl (memberP N c) x = some lx) (gx : gmoEv lx = true) : gmoLt (memberP N c) x y := by
  obtain ⟨b, -, hb⟩ := lookupOfMem hy
  obtain ⟨-, l, hl, rfl⟩ := memLblInv N c.img (cur c) x lx hx
  obtain ⟨a, hab, ha⟩ := beforeStAt pol c hv c.its.length b y x hb hxy hlt
    (.inl ⟨l, hl, by rw [← CapSync.gmoEvFix]; exact gx⟩)
  exact gmoLtOfIdx pol N c hv x y a b ha hb hab

/-- A member plain-store label is the row's. -/
theorem memberStLbl (N : Nat) (c : CandW) (e : Geid) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (kc : WmClass) (h : gxLbl (memberP N c) e = some (LStore rl base vs kc)) :
    ((cur c).rows e.1)[e.2]? = some (LStore rl base vs kc) := by
  obtain ⟨-, l, hl, he⟩ := memLblInv N c.img (cur c) e _ h
  rcases fixLblCases (rawG N c.img (cur c)) e.1 l ((cur c).fw e.1 |>.getD e.2 []) with h1 | ⟨aq, b, ts, v, rfl, h2⟩
  · rw [h1] at he; rw [hl, he]
  · rw [h2] at he; cases he

/-- **A po-earlier own plain store sharing a byte is gmo-before** (rule 1, the per-address buffer). -/
theorem memberStBefore (pol : SbPol) (N : Nat) (c : CandW) (hv : validW pol c) (x y : Geid)
    (hy : y ∈ (memberP N c).gxGmo) (hxy : x.1 = y.1) (hlt : x.2 < y.2)
    (r1 : Bool) (b1 : Int) (v1 : List (BitVec 8)) (k1 : WmClass)
    (r2 : Bool) (b2 : Int) (v2 : List (BitVec 8)) (k2 : WmClass)
    (hx : gxLbl (memberP N c) x = some (LStore r1 b1 v1 k1))
    (hy' : gxLbl (memberP N c) y = some (LStore r2 b2 v2 k2)) (a : Int) (u1 u2 : BitVec 8)
    (hx1 : gwritesByte (memberP N c) x a u1) (hy1 : gwritesByte (memberP N c) y a u2) :
    gmoLt (memberP N c) x y := by
  obtain ⟨b, -, hb⟩ := lookupOfMem hy
  obtain ⟨l1, b1', v1', j1, hl1, hw1, hv1, ha1⟩ := hx1
  obtain ⟨l2, b2', v2', j2, hl2, hw2, hv2, ha2⟩ := hy1
  rw [hx, Option.some.injEq] at hl1
  rw [hy', Option.some.injEq] at hl2
  subst hl1; subst hl2
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hw1 hw2
  obtain ⟨e1, e2⟩ := hw1
  obtain ⟨e3, e4⟩ := hw2
  subst e1; subst e2; subst e3; subst e4
  obtain ⟨a', hab, ha⟩ := beforeStAt pol c hv c.its.length b y x hb hxy hlt
    (.inr ⟨r1, b1, v1, k1, r2, b2, v2, k2, j1, j2, memberStLbl N c x _ _ _ _ hx,
      memberStLbl N c y _ _ _ _ hy', (List.getElem?_eq_some_iff.1 hv1).1,
      (List.getElem?_eq_some_iff.1 hv2).1, by rw [ha1, ha2]⟩)
  exact gmoLtOfIdx pol N c hv x y a' b ha hb hab

end CapFrame

/-! # 3. The realization interface (NAMED, P-W6) -/

/-- **REALIZATION INTERFACE (P-W6; 6a's `CapSync.floorReadReal` with the byte)**: at the post-state `σ`
of event `e`, hart `j`'s floor at a publication byte `f` naming the writer's entry at `r > 0` was raised
by a realized READ `Y` of `f` by `j` (issuing pc `ipc Y` = the ghost load-pc record's `lr j f`,
[OWN.119]) of a write at or after `r`, realized at or before `e`. -/
def CapFrame.floorByteReal (GD : Gdexec) (σ : MState) (lr : CPU → PAddr → Int) (ipc : Geid → Int)
    (j : CPU) (e : Geid) : Prop :=
  ∀ (f : PAddr) (w : CPU) (r : Nat) (v : BitVec 8) (H : Hist), j ≠ w →
    (Xv6.AccessDiscipline.xv6Env σ).isPub f w → σ.mem[f]? = some H →
    (⟨r, hartAgent w, v⟩ : HEnt) ∈ H → 0 < r → r ≤ (σ.hr j).coh f →
    ∃ (W Y : Geid), W ∈ gwrites GD.gdG ∧ r ≤ gwix GD.gdG W ∧ (W = Y ∨ gmoLt GD.gdG W Y) ∧
      Y.1 = hartAgent j ∧ ipc Y = lr j f ∧ (Y = e ∨ gmoLt GD.gdG Y e) ∧
      ∃ (t : Nat) (v' : BitVec 8), greadsByte GD.gdG Y (paZ f) t v'

/-! # 4. THE GLUE -/

namespace CapFrame

theorem gwritesLbl (G : Gexec) (W : Geid) (h : W ∈ gwrites G) :
    W ∈ G.gxGmo ∧ ∃ l, gxLbl G W = some l ∧ lbIsW l = true := by
  unfold gwrites at h
  obtain ⟨hm, hw⟩ := List.mem_filter.1 h
  refine ⟨hm, ?_⟩
  unfold gisW at hw
  cases hl : gxLbl G W with
  | none => rw [hl] at hw; cases hw
  | some l => rw [hl] at hw; exact ⟨l, rfl, hw⟩

/-- A write label is a plain store or at-event. -/
theorem wLblCases (l : Lbl) (h : lbIsW l = true) :
    (∃ rl base vs kc, l = LStore rl base vs kc) ∨ SbWalk.gmoEv l = true := by
  cases l <;> simp_all [lbIsW, SbWalk.gmoEv, SbWalk.isSt, lbIsMem, lbIsR]

/-- A read (by footprint) is at-event. -/
theorem rdGmoEv (G : Gexec) (Y : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (h : greadsByte G Y a t v) : ∃ l, gxLbl G Y = some l ∧ SbWalk.gmoEv l = true ∧
      ∀ rl base vs kc, l ≠ LStore rl base vs kc := by
  obtain ⟨l, base, ts, vs, j, hl, hr, -⟩ := h
  refine ⟨l, hl, ?_, ?_⟩
  · cases l <;> simp_all [lbRd, SbWalk.gmoEv, SbWalk.isSt, lbIsMem, lbIsR]
  · intro rl b v' kc he; subst he; simp [lbRd] at hr

theorem gposAsymm (G : Gexec) (x y : Geid) (h1 : gmoLt G x y) (h2 : gmoLt G y x) : False := by
  have := h1.2.2; have := h2.2.2; omega

/-- **THE SITE-LEVEL PUBLICATION ARM**: `j`'s observation of a publication store after the spill is a
read of a publication byte at `main+0x16`, strictly po-between the spill and the restore. -/
theorem pubInSite (pol : SbPol) (N : Nat) (c : SbWalk.CandW) (GD : Gdexec)
    (hG : GD.gdG = SbAgree.memberP N c) (hv : SbWalk.validW pol c)
    (σ : MState) (j : CPU) (pa : PAddr) (w k : Nat) (lr : CPU → PAddr → Int) (ipc : Geid → Int)
    (hP : CapSync.startedFloorPcP σ lr)
    (hRF : CapFrame.floorByteReal GD σ lr ipc j (hartAgent j, k))
    (rl : Bool) (sbase : Int) (svs : List (BitVec 8)) (skc : WmClass)
    (hSp : gxLbl GD.gdG (hartAgent j, w) = some (LStore rl sbase svs skc))
    (hSpW : (hartAgent j, w) ∈ gwrites GD.gdG)
    (raq : Bool) (rbase : Int) (rts : List Nat) (rvs : List (BitVec 8))
    (hRs : gxLbl GD.gdG (hartAgent j, k) = some (LLoad raq rbase rts rvs))
    (hkSite : ipc (hartAgent j, k) ≠ CapSync.spinLoadPc) :
    PinTrapFrame.pubSeenAfter σ j (gwix GD.gdG (hartAgent j, w)) →
    ∃ x, w < x ∧ x < k ∧ PinTrapFrame.greadsPub GD.gdG σ (hartAgent j, x) ∧
      ipc (hartAgent j, x) = CapSync.spinLoadPc := by
  rintro ⟨f, w', r, v, H, hjw, hpub, hf, he, hsr, hrc⟩
  obtain ⟨W, Y, hW, hrW, hWY, hY1, hipc, hYe, t, v', hrd⟩ :=
    hRF f w' r v H hjw hpub hf he (by omega) hrc
  have hYpc : ipc Y = CapSync.spinLoadPc := by rw [hipc]; exact hP f w' j hpub hjw (by omega)
  obtain ⟨ly, hly, gy, hyns⟩ := rdGmoEv _ Y _ t v' hrd
  have hYeq : Y = (hartAgent j, Y.2) := by rw [← hY1]
  have hYlt : gmoLt GD.gdG Y (hartAgent j, k) := by
    rcases hYe with h | h
    · exfalso; rw [h] at hYpc; exact hkSite hYpc
    · exact h
  have hgr : SbWalk.gmoEv (LLoad raq rbase rts rvs) = true := rfl
  rw [hG] at hYlt hly hRs
  have hYk : Y.2 < k :=
    CapSync.memberPoOfGmo pol N c hv Y (hartAgent j, k) ly _ hYlt hY1 hly gy hRs hgr
  refine ⟨Y.2, ?_, hYk, ⟨f, w', t, v', hpub, (by rw [← hYeq]; exact hrd)⟩, (by rw [← hYeq]; exact hYpc)⟩
  -- po-after the spill: a po-earlier read is gmo-before the spill's landing
  have hnd := memberNodup pol N c hv
  obtain ⟨hSpm, -⟩ := gwritesLbl _ _ hSpW
  have hsW : gpos GD.gdG (hartAgent j, w) < gpos GD.gdG W := by
    have := (gwixGposLt GD.gdG _ W (by rw [hG]; exact hnd) hSpW hW).1 (by omega)
    exact this
  have hsY : gpos GD.gdG (hartAgent j, w) < gpos GD.gdG Y := by
    rcases hWY with h | h
    · rw [← h]; exact hsW
    · exact Nat.lt_trans hsW h.2.2
  rcases Nat.lt_trichotomy Y.2 w with h | h | h
  · exfalso
    rw [hG] at hSpm hsY
    have := memberEvBefore pol N c hv Y (hartAgent j, w) ly hSpm hY1 h hly gy
    have := this.2.2
    omega
  · exfalso
    rw [hYeq, h] at hly
    rw [hG] at hSp
    rw [hSp, Option.some.injEq] at hly
    exact hyns _ _ _ _ hly.symm
  · exact h

/-- **`pubSeenAfter` REFUTED BY THE SITE CENSUS**: if no event of `j` strictly between the spill and the
restore is issued at `main+0x16` (`PinTrapFrame.frameWindowsNoStarted` over the window's items), `j`
observed no publication store after the spill. -/
theorem k2OfSite (pol : SbPol) (N : Nat) (c : SbWalk.CandW) (GD : Gdexec)
    (hG : GD.gdG = SbAgree.memberP N c) (hv : SbWalk.validW pol c)
    (σ : MState) (j : CPU) (pa : PAddr) (w k : Nat) (lr : CPU → PAddr → Int) (ipc : Geid → Int)
    (hP : CapSync.startedFloorPcP σ lr)
    (hRF : CapFrame.floorByteReal GD σ lr ipc j (hartAgent j, k))
    (rl : Bool) (sbase : Int) (svs : List (BitVec 8)) (skc : WmClass)
    (hSp : gxLbl GD.gdG (hartAgent j, w) = some (LStore rl sbase svs skc))
    (hSpW : (hartAgent j, w) ∈ gwrites GD.gdG)
    (raq : Bool) (rbase : Int) (rts : List Nat) (rvs : List (BitVec 8))
    (hRs : gxLbl GD.gdG (hartAgent j, k) = some (LLoad raq rbase rts rvs))
    (hkSite : ipc (hartAgent j, k) ≠ CapSync.spinLoadPc)
    (hQ : ∀ x, w < x → x < k → ipc (hartAgent j, x) ≠ CapSync.spinLoadPc) :
    ¬ PinTrapFrame.pubSeenAfter σ j (gwix GD.gdG (hartAgent j, w)) := fun h =>
  let ⟨x, h1, h2, _, h4⟩ := pubInSite pol N c GD hG hv σ j pa w k lr ipc hP hRF rl sbase svs skc hSp
    hSpW raq rbase rts rvs hRs hkSite h
  hQ x h1 h2 h4

/-- **THE GLUE — A9 `FrameWin` AT THE `SbCand` MEMBER**: from 6a's two interim premises and
interfaces (at the restore), GF's `.aq` image fact, the store-side row order (§1), the floor-read
interface (§3) and the restore's site fact. -/
theorem frameWinOf (pol : SbPol) (N : Nat) (c : SbWalk.CandW) (GD : Gdexec)
    (hG : GD.gdG = SbAgree.memberP N c) (hv : SbWalk.validW pol c)
    (σ : MState) (j : CPU) (pa : PAddr) (w k : Nat) (lr : CPU → PAddr → Int) (ipc : Geid → Int)
    (hAq : CapSync.amoAqAt GD.gdG) (hL : CapSync.lockNzExclP σ) (hP : CapSync.startedFloorPcP σ lr)
    (hRA : CapSync.exclHopReal GD σ) (hRB : CapSync.realBefore GD σ (hartAgent j, k))
    (hRF : CapFrame.floorByteReal GD σ lr ipc j (hartAgent j, k))
    (rl : Bool) (sbase : Int) (svs : List (BitVec 8)) (skc : WmClass)
    (hSp : gxLbl GD.gdG (hartAgent j, w) = some (LStore rl sbase svs skc))
    (hSpW : (hartAgent j, w) ∈ gwrites GD.gdG)
    (hSpb : ∃ v, gwritesByte GD.gdG (hartAgent j, w) (paZ pa) v)
    (raq : Bool) (rbase : Int) (rts : List Nat) (rvs : List (BitVec 8))
    (hRs : gxLbl GD.gdG (hartAgent j, k) = some (LLoad raq rbase rts rvs))
    (hkSite : ipc (hartAgent j, k) ≠ CapSync.spinLoadPc) :
    PinTrapFrame.FrameWin GD.gdG σ j pa (gwix GD.gdG (hartAgent j, w)) w k := by
  have hnd : GD.gdG.gxGmo.Nodup := by rw [hG]; exact memberNodup pol N c hv
  obtain ⟨hSpm, -⟩ := gwritesLbl _ _ hSpW
  have hgr : SbWalk.gmoEv (LLoad raq rbase rts rvs) = true := rfl
  -- a write gwix-after the spill is gpos-after it
  have hafter : ∀ W, W ∈ gwrites GD.gdG → gwix GD.gdG (hartAgent j, w) < gwix GD.gdG W →
      gpos GD.gdG (hartAgent j, w) < gpos GD.gdG W :=
    fun W hW h => (gwixGposLt GD.gdG _ W hnd hSpW hW).1 h
  -- an at-event write of `j` gmo-after the spill is po-after it
  have evAfter : ∀ W lw, W.1 = hartAgent j → gxLbl GD.gdG W = some lw → SbWalk.gmoEv lw = true →
      gpos GD.gdG (hartAgent j, w) < gpos GD.gdG W → w < W.2 := by
    intro W lw hW1 hlw gw hpos
    rcases Nat.lt_trichotomy W.2 w with h | h | h
    · exfalso
      have hm := hSpm; rw [hG] at hm; rw [hG] at hlw
      have := (memberEvBefore pol N c hv W (hartAgent j, w) lw hm hW1 h hlw gw).2.2
      rw [hG] at hpos; omega
    · exfalso
      have : W = (hartAgent j, w) := by rw [← hW1, ← h]
      rw [this, hSp, Option.some.injEq] at hlw
      subst hlw; simp [SbWalk.gmoEv, SbWalk.isSt] at gw
    · exact h
  -- a write of `j` realized before the restore is po-before it
  have wBefore : ∀ W lw, W ∈ gwrites GD.gdG → W.1 = hartAgent j → gxLbl GD.gdG W = some lw →
      gwix GD.gdG W ≤ σ.top → W.2 < k := by
    intro W lw hW hW1 hlw htop
    have hww : lbIsW lw = true := by
      obtain ⟨-, l', hl', hw'⟩ := gwritesLbl _ _ hW
      rw [hlw, Option.some.injEq] at hl'; subst hl'; exact hw'
    rcases hRB W hW htop with h | h
    · exfalso; rw [h, hRs, Option.some.injEq] at hlw; subst hlw; simp [lbIsW] at hww
    · rcases wLblCases lw hww with ⟨rl', b', vs', kc', rfl⟩ | gw
      · rcases Nat.lt_trichotomy W.2 k with h' | h' | h'
        · exact h'
        · exfalso
          have : W = (hartAgent j, k) := by rw [← hW1, ← h']
          rw [this, hRs, Option.some.injEq] at hlw; cases hlw
        · exfalso
          have hm := h.1; rw [hG] at hm h; rw [hG] at hRs
          exact gposAsymm _ _ _ h
            (memberEvBefore pol N c hv (hartAgent j, k) W _ hm hW1.symm h' hRs hgr)
      · have h2 := h; rw [hG] at h2 hlw; rw [hG] at hRs
        exact CapSync.memberPoOfGmo pol N c hv W (hartAgent j, k) lw _ h2 hW1 hlw gw hRs hgr
  refine ⟨fun W hW hW1 hsW htop hhop => ?_, fun h => ?_, fun W hW hW1 hsW htop hby => ?_⟩
  · -- acqIn: the hop's acquire is an exclusive write, hence an AMO, hence `.aq`
    obtain ⟨b, C, r, hhb, hsh⟩ := hhop
    have hpc := hL b C j r _ hhb hsh
    obtain ⟨aq, rl', base, ts, rvs', wvs, kc, hlb⟩ := hRA W b C j r hW hW1 hhb hsh hpc
    have haq := hAq W aq rl' base ts rvs' wvs kc hlb
    subst haq
    refine ⟨⟨_, hlb, rfl⟩, evAfter W _ hW1 hlb rfl (hafter W hW hsW), wBefore W _ hW hW1 hlb htop⟩
  · -- pubIn: the site-level arm
    obtain ⟨x, h1, h2, h3, -⟩ := pubInSite pol N c GD hG hv σ j pa w k lr ipc hP hRF rl sbase svs skc
      hSp hSpW raq rbase rts rvs hRs hkSite h
    exact ⟨x, h1, h2, h3⟩
  · -- ownIn: an AMO arm as `acqIn`; a plain store to `pa` lands after an older own store to `pa`
    obtain ⟨-, lw, hlw, hww⟩ := gwritesLbl _ _ hW
    refine ⟨?_, wBefore W lw hW hW1 hlw htop⟩
    rcases wLblCases lw hww with ⟨rl', b', vs', kc', rfl⟩ | gw
    · rcases Nat.lt_trichotomy W.2 w with h | h | h
      · exfalso
        obtain ⟨u1, hu1⟩ := hby
        obtain ⟨u2, hu2⟩ := hSpb
        have hm := hSpm
        rw [hG] at hm hlw hSp hu1 hu2
        have := (memberStBefore pol N c hv W (hartAgent j, w) hm hW1 h _ _ _ _ _ _ _ _ hlw hSp _ u1 u2
          hu1 hu2).2.2
        have h' := hafter W hW hsW
        rw [hG] at h'; omega
      · exfalso
        have : W = (hartAgent j, w) := by rw [← hW1, ← h]
        rw [this] at hsW; omega
      · exact h
    · exact evAfter W lw hW1 hlw gw (hafter W hW hsW)

end CapFrame
end Weak
