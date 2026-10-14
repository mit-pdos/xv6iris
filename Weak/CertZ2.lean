/-
Weak: **W10-2 [OWN.94] (N2′), increment 3 — THE FREE WALK at the Zifencei threaded state**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

N2′'s tail walk (`CatLin.tailPolicyCZ`, `Weak/GraphFetchN2.lean`) does NOT walk a given graph's gmo
(the pinned walk `wlkRun` and `GraphFetchWalkZ.wlkRunZ'` append `G`'s `(n+1)`-st write at each
step, which forces `gwrowGmo G`, the W10 sizing's headline): it walks hart rows in an order the
POLICY chooses (po ∪ co_L on the tail, spike (1)), and the realized member `GR` is read off the
final candidate.  This file is that walk's engine:

  §1  the per-hart slot counters (`CertZ2.bump`) and the termination measure `CertZ2.rem` (the
      slots left, `CertZ2.remStep`);
  §2  the step obligation `CertZ2.stepOkZ` (what `CertZ.cstOkZWSnoc` consumes, packaged) and the
      walk policy **`CertZ2.walkPolZ`**: at every invariant state with an unfinished hart, the
      policy picks a hart `x`, its next row label, the appended label (`lblReidxW`), the step's
      obligations, and keeps its invariant `Inv`;
  §3  **`CertZ2.walkRunZ`** — THE ITERATION: from any invariant state, a `segsRunZ` of one-slot
      segments to a state where every hart's row is finished, each hart's appended labels being
      `lblReidxW` of its remaining row (the per-hart filter of the appended trace).

Spec: proof organisation (FAITHFUL, no trusted text).  Lean-only helpers file-qualified
(`CertZ2.*`).
-/
import Weak.CertZ

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Counters and the measure -/

/-- Hart `x`'s counter advanced by one slot. -/
def CertZ2.bump (cnt : Nat → Nat) (x : Nat) : Nat → Nat :=
  fun y => if y = x then cnt y + 1 else cnt y

theorem CertZ2.bumpSelf (cnt : Nat → Nat) (x : Nat) : CertZ2.bump cnt x x = cnt x + 1 := by
  simp [CertZ2.bump]

theorem CertZ2.bumpNe (cnt : Nat → Nat) (x y : Nat) : y ≠ x → CertZ2.bump cnt x y = cnt y := by
  intro h; simp [CertZ2.bump, h]

/-- The slots left over harts `0 … n-1`. -/
def CertZ2.rem (n : Nat) (len cnt : Nat → Nat) : Nat :=
  ((List.range n).map (fun x => len x - cnt x)).sum

theorem CertZ2.remStep (len cnt : Nat → Nat) (x : Nat) :
    ∀ n, x < n → cnt x < len x →
      CertZ2.rem n len (CertZ2.bump cnt x) + 1 = CertZ2.rem n len cnt := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro hx hc
    unfold CertZ2.rem
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    by_cases hxn : x < n
    · have h1 := ih hxn hc
      unfold CertZ2.rem at h1
      rw [CertZ2.bumpNe cnt x n (by omega)]
      omega
    · have hxe : x = n := by omega
      subst hxe
      have hpre : (List.range x).map (fun y => len y - CertZ2.bump cnt x y) =
          (List.range x).map (fun y => len y - cnt y) := by
        apply List.map_congr_left
        intro y hy
        rw [CertZ2.bumpNe cnt x y (by have := List.mem_range.1 hy; omega)]
      rw [hpre, CertZ2.bumpSelf]
      omega

/-! # 2. The step obligation and the walk policy -/

/-- What `CertZ.cstOkZWSnoc` consumes for hart `x`'s appended label `lb'`, from its program state
`pC` to `pC'`, the fabric moving to `d'`. -/
def CertZ2.stepOkZ (St : CycState) (itvOf : Nat → Nat → Nat) (x : Nat) (lb' : Lbl)
    (pC pa : Pexv6) (da : Efab) (ls : List Wlabel) (pC' : Pexv6) (d' : Efab) : Prop :=
    mstepOk (candLastSt St.cstC) x lb' ∧
    (∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      lb' = .LLoad aq base ts vs →
      scaOkT (shadowOf cohSrc St.cstC.cdTr x) (candLastSt St.cstC).msImg
          (candLastSt St.cstC).msLog x base ts ∧
        diskLatOk (candLastSt St.cstC).msImg (candLastSt St.cstC).msLog x base ts) ∧
    admRunG pstepEv true pC (St.cstDv (cdEnd St.cstC)) ls pa da ∧
    (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
      PfRunUnpinned.fcutM2 (itvOf (cdEnd St.cstC) x) (candLastSt St.cstC).msImg
        (candLastSt St.cstC).msLog x base tvs) ∧
    ((∃ l, lbFused l ∧ lblRealizes pclsEv pa (candLastSt St.cstC) x lb' l ∧
        pstepEv pa da l pC' d') ∨
     (∃ (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab)
        (l1 l2 : Wlabel),
        lblRealizesPair pclsEv pa pm2 (candLastSt St.cstC) x lb' l1 l2 ∧
        pstepEv pa da l1 pm dm ∧
        admRunG pstepEv false pm dm ls2 pm2 dm2 ∧
        pstepEv pm2 dm2 l2 pC' d'))

/-- The appended state. -/
def CertZ2.stSnoc (St : CycState) (x : Nat) (lb' : Lbl) (pC' : Pexv6) (d' : Efab) : CycState :=
  ⟨candSnoc St.cstC ⟨x, lb'⟩, pstSnoc St.cstC St.cstPst x pC', dvSnoc St.cstC St.cstDv d'⟩

/-- The walk invariant's carrier: the state, its instruction views, the slot counters. -/
abbrev CertZ2.WInv : Type :=
  CycState → (Nat → Nat → Nat) → (Nat → Nat → Bool) → (Nat → Nat) → Prop

/-- **THE WALK POLICY** (N2′'s tail walk, at an invariant `Inv` over states, instruction views and
slot counters): whenever some hart `x < rows.length` has slots left, the policy picks such a hart,
its next row label `lb`, the appended label `lb'` (`lblReidxW lb lb'`), the step's block (leading
star `ls`), discharges the step and keeps `Inv` at the advanced counters and the views extended by
M2's recurrence (`CertZ.itvSnoc`/`CertZ.fiSnoc` at `ls`).  The choice of `x` IS the walk order
(po ∪ co_L, spike (1)). -/
def CertZ2.walkPolZ (d0 : Efab) (rows : List (List Lbl)) (Inv : CertZ2.WInv) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (cnt : Nat → Nat),
    CertZ.cstOkZW d0 St itvOf fiOf → Inv St itvOf fiOf cnt →
    (∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length) →
    ∃ (x : Nat) (lb lb' : Lbl) (pC pa : Pexv6) (da : Efab) (ls : List Wlabel) (pC' : Pexv6)
      (d' : Efab),
      x < rows.length ∧ (rows.getD x [])[cnt x]? = some lb ∧
      (St.cstPst (cdEnd St.cstC))[x]? = some pC ∧
      lblReidxW lb lb' ∧ CertZ2.stepOkZ St itvOf x lb' pC pa da ls pC' d' ∧
      Inv (CertZ2.stSnoc St x lb' pC' d') (CertZ.itvSnoc St.cstC ⟨x, lb'⟩ ls itvOf fiOf)
        (CertZ.fiSnoc St.cstC ⟨x, lb'⟩ ls fiOf) (CertZ2.bump cnt x)

/-! # 3. THE ITERATION -/

/-- The per-hart filter of a trace. -/
def CertZ2.hartTr (tr : List Estep) (x : Nat) : List Lbl :=
  (tr.filter (fun s => decide (s.esAg = x))).map (fun s => s.esLb)

theorem CertZ2.hartTrCons (s : Estep) (tr : List Estep) (x : Nat) :
    CertZ2.hartTr (s :: tr) x =
      if s.esAg = x then s.esLb :: CertZ2.hartTr tr x else CertZ2.hartTr tr x := by
  by_cases h : s.esAg = x <;> simp [CertZ2.hartTr, h]

/-- **`CertZ2.walkRunZ` — THE FREE WALK**: from an invariant state, the walk runs to a state where
every hart's row is finished; each hart's appended labels are `lblReidxW` of its remaining row. -/
theorem CertZ2.walkRunZ (d0 : Efab) (rows : List (List Lbl))
    (Inv : CertZ2.WInv) (hpol : CertZ2.walkPolZ d0 rows Inv) :
    ∀ (m : Nat) (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
      (cnt : Nat → Nat),
      CertZ2.rem rows.length (fun x => (rows.getD x []).length) cnt ≤ m →
      CertZ.cstOkZW d0 St itvOf fiOf → Inv St itvOf fiOf cnt →
      ∃ (l : List Segout) (Sf : CycState) (itvOf' : Nat → Nat → Nat)
        (fiOf' : Nat → Nat → Bool) (cntF : Nat → Nat) (tradd : List Estep),
        segsRunZ d0 l St Sf ∧ CertZ.cstOkZW d0 Sf itvOf' fiOf' ∧ Inv Sf itvOf' fiOf' cntF ∧
        (∀ x, x < rows.length → (rows.getD x []).length ≤ cntF x) ∧
        (∀ x, cnt x ≤ cntF x) ∧
        Sf.cstC.cdTr = St.cstC.cdTr ++ tradd ∧
        (∀ x, List.Forall₂ lblReidxW (((rows.getD x []).drop (cnt x)).take (cntF x - cnt x))
          (CertZ2.hartTr tradd x)) ∧
        (∀ s, s ∈ tradd → s.esAg < rows.length) ∧
        Sf.cstC.cdImg = St.cstC.cdImg ∧ Sf.cstPst 0 = St.cstPst 0 := by
  intro m
  induction m with
  | zero =>
    intro St itvOf fiOf cnt hm hok hinv
    refine ⟨[], St, itvOf, fiOf, cnt, [], .segsDone St (CertZ.cstOkZOfW _ _ _ _ hok), hok, hinv,
      ?_, fun _ => Nat.le_refl _, (List.append_nil _).symm, ?_, fun s h => by simp at h, rfl, rfl⟩
    · intro x hx
      refine Nat.le_of_not_lt (fun hlt => ?_)
      have := CertZ2.remStep (fun x => (rows.getD x []).length) cnt x rows.length hx hlt
      omega
    · intro x
      simp [CertZ2.hartTr]
  | succ m ih =>
    intro St itvOf fiOf cnt hm hok hinv
    by_cases hd : ∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length
    · obtain ⟨x, lb, lb', pC, pa, da, ls, pC', d', hx, hlb, hp, hre, ⟨hmok, hld, hrun, hcut, harm⟩,
        hinv1⟩ := hpol St itvOf fiOf cnt hok hinv hd
      have hcx : cnt x < (rows.getD x []).length := lookup_lt_Some hlb
      have hok1 := CertZ.cstOkZWSnoc d0 St itvOf fiOf x lb' pC pa da ls pC' d' hok hmok hld hp
        hrun hcut harm
      have hrem := CertZ2.remStep (fun x => (rows.getD x []).length) cnt x rows.length hx hcx
      obtain ⟨l, Sf, itvOf', fiOf', cntF, tradd, hrun', hokF, hinvF, hdone, hmono, htr, hf2,
        hagt, himg, hpst⟩ := ih (CertZ2.stSnoc St x lb' pC' d') _ _ (CertZ2.bump cnt x) (by omega) hok1
          hinv1
      have hstep : segStepZ d0 ⟨x, [lb], cdEnd St.cstC, [⟨x, lb'⟩]⟩ St
          (CertZ2.stSnoc St x lb' pC' d') :=
        ⟨CertZ.cstOkZOfW _ _ _ _ hok, CertZ.cstOkZOfW _ _ _ _ hok1, rfl, rfl,
          fun s hs => by simp at hs; rw [hs], .cons hre .nil⟩
      have hmonoF : ∀ y, cnt y ≤ cntF y := by
        intro y
        have := hmono y
        by_cases hy : y = x
        · subst hy; rw [CertZ2.bumpSelf] at this; omega
        · rw [CertZ2.bumpNe cnt x y hy] at this; exact this
      refine ⟨_ :: l, Sf, itvOf', fiOf', cntF, ⟨x, lb'⟩ :: tradd,
        .segsMore _ l St _ Sf hstep hrun', hokF, hinvF, hdone, hmonoF, ?_, ?_, ?_, ?_, ?_⟩
      · rw [htr]
        show (St.cstC.cdTr ++ [⟨x, lb'⟩]) ++ tradd = St.cstC.cdTr ++ ⟨x, lb'⟩ :: tradd
        simp
      · intro y
        rw [CertZ2.hartTrCons]
        have hfy := hf2 y
        by_cases hy : x = y
        · subst hy
          rw [if_pos rfl, CertZ2.bumpSelf] at *
          have hge : cnt x + 1 ≤ cntF x := by
            have := hmono x; rw [CertZ2.bumpSelf] at this; exact this
          rw [CertZ.dropCons _ (cnt x) lb hlb,
            show cntF x - cnt x = (cntF x - (cnt x + 1)) + 1 by omega, List.take_succ_cons]
          exact .cons hre hfy
        · rw [if_neg hy]
          rw [CertZ2.bumpNe cnt x y (Ne.symm hy)] at hfy
          exact hfy
      · intro s hs
        rcases List.mem_cons.1 hs with rfl | hs
        · exact hx
        · exact hagt s hs
      · rw [himg]; rfl
      · rw [hpst]
        exact pstSnocLe St.cstC St.cstPst x pC' 0 (Nat.zero_le _)
    · refine ⟨[], St, itvOf, fiOf, cnt, [], .segsDone St (CertZ.cstOkZOfW _ _ _ _ hok), hok,
        hinv, ?_, fun _ => Nat.le_refl _, (List.append_nil _).symm, ?_, fun s h => by simp at h,
        rfl, rfl⟩
      · intro x hx
        exact Nat.le_of_not_lt (fun hlt => hd ⟨x, hx, hlt⟩)
      · intro x
        simp [CertZ2.hartTr]

end Weak
