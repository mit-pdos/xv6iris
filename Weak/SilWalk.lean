/-
Weak: **(c) [OWN.100], increment 5c-i — the twin walk state and its one-step extension**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The twin of `CycState` / `CertZ.cstOkZW` / `CertZ2.stepOkZ` / `CertZ.cstOkZWSnoc` over a TWIN candidate
(`SilCand.CandS`) and the twin program data (`SilReplay.progOk`): no instruction views / cut clause
(the twin replay needs only the view-0 fetch check), and an appended step may be SILENT (`some q`).

  `SilWalk.St`, **`SilWalk.ok`** (sil column as long as the trace, `validS`, `progOk`, fabric starts at
  `d0`), `SilWalk.snoc`, **`SilWalk.stepOk`** (what the appended step owes at the current last state),
  `SilWalk.stAtSnoc` (the old states are unchanged), **`SilWalk.okSnoc`** (the one-step extension),
  `SilWalk.start` / `SilWalk.okStart`.

Spec: FAITHFUL (proof organisation).
-/
import Weak.SilKill

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-- The twin walk state: a twin candidate, its program states and fabric per index, and its
dependency shadow (each agent's pf state per index). -/
structure SilWalk.St where
  c : SilCand.CandS
  pst : Nat → List Pexv6
  dv : Nat → Efab
  sh : Nat → Nat → Wstate

/-- **THE TWIN THREADED STATE.** -/
def SilWalk.ok (d0 : Efab) (S : SilWalk.St) : Prop :=
  S.c.sil.length = S.c.tr.length ∧ SilCand.validS S.c ∧
  SilReplay.progOkD pstepEv pclsEv S.pst S.dv S.sh S.c ∧ S.dv 0 = d0

/-- The appended state: hart `x`'s step `lb`, silent at `o`, program state `pC'`, fabric `d'`, hart
`x`'s new shadow state `w'`. -/
def SilWalk.snoc (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6) (d' : Efab)
    (w' : Wstate) : SilWalk.St :=
  ⟨⟨S.c.img, S.c.tr ++ [⟨x, lb⟩], S.c.sil ++ [o]⟩,
   fun k => if k ≤ S.c.tr.length then S.pst k else (S.pst S.c.tr.length).set x pC',
   fun k => if k ≤ S.c.tr.length then S.dv k else d',
   fun k => if k ≤ S.c.tr.length then S.sh k else
     fun j => if j = x then w' else S.sh S.c.tr.length j⟩

theorem SilWalk.snocShOld (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6)
    (d' : Efab) (w' : Wstate) (k : Nat) :
    k ≤ S.c.tr.length → (SilWalk.snoc S x lb o pC' d' w').sh k = S.sh k :=
  fun h => if_pos h

theorem SilWalk.snocShNew (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6)
    (d' : Efab) (w' : Wstate) :
    (SilWalk.snoc S x lb o pC' d' w').sh (S.c.tr.length + 1)
      = fun j => if j = x then w' else S.sh S.c.tr.length j :=
  if_neg (by omega)

/-- **WHAT AN APPENDED STEP OWES** at the current last state `stAt c |tr|`: validity (an ordinary step
is `mstepOk`, a silent one an `LRmw … false` with `silentOk`), the leading star from `pC` with its
fetches at their view-0 check, and the realization (one label, ordinary steps only; or the pair) with
hart `x`'s new shadow state `w'` (at a silent step: the dependency bound, `SilDep.pairSh`). -/
def SilWalk.stepOk (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC pa : Pexv6)
    (da : Efab) (ls : List Wlabel) (pC' : Pexv6) (d' : Efab) (w' : Wstate) : Prop :=
  (o = none → mstepOk (SilCand.stAt S.c S.c.tr.length) x lb) ∧
  (∀ q, o = some q →
    ∃ aq base ts rvs wvs kc, lb = .LRmw aq false base ts rvs wvs kc ∧
      SilCand.silentOk (SilCand.stAt S.c S.c.tr.length) x aq base ts rvs wvs q) ∧
  admRunG pstepEv true pC (S.dv S.c.tr.length) ls pa da ∧
  (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
    ifetchOk (SilCand.stAt S.c S.c.tr.length).msImg (SilCand.stAt S.c S.c.tr.length).msLog 0
      base tvs) ∧
  ((o = none ∧ ∃ l, lblRealizes pclsEv pa (SilCand.stAt S.c S.c.tr.length) x lb l ∧
      pstepEv pa da l pC' d' ∧
      w' = SilDep.wsStep (SilDep.starWs (S.sh S.c.tr.length x) ls
        (SilCand.stAt S.c S.c.tr.length).msLog.length) l
        (SilCand.stAt S.c S.c.tr.length).msLog.length)
   ∨ (∃ (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
        lblRealizesPair pclsEv pa pm2 (SilCand.stAt S.c S.c.tr.length) x lb l1 l2 ∧
        pstepEv pa da l1 pm dm ∧
        admRunG pstepEv false pm dm ls2 pm2 dm2 ∧
        pstepEv pm2 dm2 l2 pC' d' ∧
        SilDep.pairSh (S.sh S.c.tr.length x) ls l1 ls2 l2
          (SilCand.stAt S.c S.c.tr.length).msLog.length o w'))

theorem SilWalk.getDApp {A : Type _} (l m : List A) (k : Nat) (d : A) :
    k < l.length → (l ++ m).getD k d = l.getD k d := by
  intro h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem SilWalk.getDAppEnd {A : Type _} (l : List A) (a d : A) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

/-- The old states are unchanged by appending. -/
theorem SilWalk.stAtSnoc (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat) (pC' : Pexv6)
    (d' : Efab) (w' : Wstate) :
    S.c.sil.length = S.c.tr.length →
    ∀ k, k ≤ S.c.tr.length →
      SilCand.stAt (SilWalk.snoc S x lb o pC' d' w').c k = SilCand.stAt S.c k := by
  intro hsl k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ : ∃ s, S.c.tr[k]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs' : (SilWalk.snoc S x lb o pC' d' w').c.tr[k]? = some s := by
      show (S.c.tr ++ [⟨x, lb⟩])[k]? = some s
      rw [List.getElem?_append_left (by omega)]; exact hs
    have hsil : (SilWalk.snoc S x lb o pC' d' w').c.sil.getD k none = S.c.sil.getD k none :=
      SilWalk.getDApp _ _ _ _ (by omega)
    rw [SilReplay.stAtSucc _ k s hs', SilReplay.stAtSucc _ k s hs, hsil, ih (by omega)]

/-- **THE ONE-STEP EXTENSION.** -/
theorem SilWalk.okSnoc (d0 : Efab) (S : SilWalk.St) (x : Nat) (lb : Lbl) (o : Option Nat)
    (pC pa : Pexv6) (da : Efab) (ls : List Wlabel) (pC' : Pexv6) (d' : Efab) (w' : Wstate) :
    SilWalk.ok d0 S → (S.pst S.c.tr.length)[x]? = some pC →
    SilWalk.stepOk S x lb o pC pa da ls pC' d' w' →
    SilWalk.ok d0 (SilWalk.snoc S x lb o pC' d' w') := by
  rintro ⟨hsl, hv, hpr, hd0⟩ hp ⟨hok, hsil, hstar, hfetch, harm⟩
  have hst := SilWalk.stAtSnoc S x lb o pC' d' w' hsl
  -- the trace lookup splits into the old indices and the new one
  have hsplit : ∀ k s, (SilWalk.snoc S x lb o pC' d' w').c.tr[k]? = some s →
      (k < S.c.tr.length ∧ S.c.tr[k]? = some s) ∨ (k = S.c.tr.length ∧ s = ⟨x, lb⟩) := by
    intro k s hs
    change (S.c.tr ++ [⟨x, lb⟩])[k]? = some s at hs
    have hlt := lookup_lt_Some hs
    simp only [List.length_append, List.length_singleton] at hlt
    by_cases hk : k < S.c.tr.length
    · rw [List.getElem?_append_left hk] at hs
      exact .inl ⟨hk, hs⟩
    · have hke : k = S.c.tr.length := by omega
      subst hke
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hs
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      exact .inr ⟨rfl, hs.symm⟩
  have hsilOld : ∀ k, k < S.c.tr.length →
      (SilWalk.snoc S x lb o pC' d' w').c.sil.getD k none = S.c.sil.getD k none :=
    fun k hk => SilWalk.getDApp _ _ _ _ (by omega)
  have hsilNew : (SilWalk.snoc S x lb o pC' d' w').c.sil.getD S.c.tr.length none = o := by
    show (S.c.sil ++ [o]).getD S.c.tr.length none = o
    rw [← hsl]; exact SilWalk.getDAppEnd _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (S.c.sil ++ [o]).length = (S.c.tr ++ [(⟨x, lb⟩ : Estep)]).length
    simp [hsl]
  · intro k s hs
    rcases hsplit k s hs with ⟨hk, hs0⟩ | ⟨rfl, rfl⟩
    · rw [hsilOld k hk, hst k (by omega)]
      exact hv k s hs0
    · rw [hsilNew, hst _ (Nat.le_refl _)]
      exact ⟨hok, hsil⟩
  · refine ⟨fun j => by rw [SilWalk.snocShOld _ _ _ _ _ _ _ _ (Nat.zero_le _)]; exact hpr.1 j, ?_⟩
    intro k s hs
    rcases hsplit k s hs with ⟨hk, hs0⟩ | ⟨rfl, rfl⟩
    · obtain ⟨p, pa0, da0, p', ls0, h1, h2, h3, h4, h5, h6⟩ := hpr.2 k s hs0
      have g0 : (SilWalk.snoc S x lb o pC' d' w').sh k = S.sh k :=
        SilWalk.snocShOld _ _ _ _ _ _ _ _ (by omega)
      have g1 : (SilWalk.snoc S x lb o pC' d' w').sh (k + 1) = S.sh (k + 1) :=
        SilWalk.snocShOld _ _ _ _ _ _ _ _ (by omega)
      have e0 : (SilWalk.snoc S x lb o pC' d' w').pst k = S.pst k := if_pos (by omega)
      have e1 : (SilWalk.snoc S x lb o pC' d' w').pst (k + 1) = S.pst (k + 1) := if_pos (by omega)
      have f0 : (SilWalk.snoc S x lb o pC' d' w').dv k = S.dv k := if_pos (by omega)
      have f1 : (SilWalk.snoc S x lb o pC' d' w').dv (k + 1) = S.dv (k + 1) := if_pos (by omega)
      refine ⟨p, pa0, da0, p', ls0, by rw [e0]; exact h1, by rw [e1, e0]; exact h2,
        by rw [f0]; exact h3, by rw [hst k (by omega)]; exact h4, ?_,
        fun j hj => by rw [g0, g1]; exact h6 j hj⟩
      rw [hsilOld k hk, hst k (by omega), f1, g0, g1]
      exact h5
    · have e0 : (SilWalk.snoc S x lb o pC' d' w').pst S.c.tr.length = S.pst S.c.tr.length :=
        if_pos (Nat.le_refl _)
      have e1 : (SilWalk.snoc S x lb o pC' d' w').pst (S.c.tr.length + 1)
          = (S.pst S.c.tr.length).set x pC' := if_neg (by omega)
      have f0 : (SilWalk.snoc S x lb o pC' d' w').dv S.c.tr.length = S.dv S.c.tr.length :=
        if_pos (Nat.le_refl _)
      have f1 : (SilWalk.snoc S x lb o pC' d' w').dv (S.c.tr.length + 1) = d' := if_neg (by omega)
      have g0 : (SilWalk.snoc S x lb o pC' d' w').sh S.c.tr.length = S.sh S.c.tr.length :=
        SilWalk.snocShOld _ _ _ _ _ _ _ _ (Nat.le_refl _)
      have gx : (SilWalk.snoc S x lb o pC' d' w').sh (S.c.tr.length + 1)
          (Estep.esAg ⟨x, lb⟩) = w' := by
        rw [SilWalk.snocShNew]; exact if_pos rfl
      refine ⟨pC, pa, da, pC', ls, by rw [e0]; exact hp, by rw [e1, e0], by rw [f0]; exact hstar,
        by rw [hst _ (Nat.le_refl _)]; exact hfetch, ?_, fun j hj => ?_⟩
      · rw [hsilNew, hst _ (Nat.le_refl _), f1, g0, gx]
        exact harm
      · rw [SilWalk.snocShNew, g0]
        exact if_neg hj
  · show (if 0 ≤ S.c.tr.length then S.dv 0 else d') = d0
    rw [if_pos (Nat.zero_le _)]; exact hd0

/-- The start: the empty twin candidate over the graph's image. -/
def SilWalk.start (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) : SilWalk.St :=
  ⟨⟨G.gxImg, [], []⟩, fun _ => (List.range' 0 N).map boot, fun _ => d0, fun _ _ => wsInit⟩

theorem SilWalk.okStart (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) :
    SilWalk.ok d0 (SilWalk.start boot d0 N G) := by
  refine ⟨rfl, fun k s hs => ?_, ⟨fun _ => rfl, fun k s hs => ?_⟩, rfl⟩
  · simp [SilWalk.start] at hs
  · simp [SilWalk.start] at hs

/-- A finished twin walk state IS a twin run datum. -/
theorem SilWalk.runDataOfOk (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (S : SilWalk.St) :
    SilWalk.ok d0 S → S.c.img = G.gxImg → S.pst 0 = (List.range' 0 N).map boot →
    SilAgree.RunDataS boot d0 N G S.c S.pst S.dv :=
  fun ⟨_, hv, hpr, hd0⟩ himg hpst => ⟨hv, himg, hpst, hd0, ⟨S.sh, hpr⟩⟩

end Weak
