/-
Weak: **W10 F1 [OWN.94] (N2′), decision (A), step 3a — THE WALK WITH SKIP STEPS**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The walk SKIPS exactly the failed-acquire slots (`CertZ24.lblFail`): such a slot advances the hart's
counter and appends nothing to the candidate.  **`CertZ26.walkPolZ4`** (the policy with skip steps) and
**`CertZ26.walkRunZ4`** (the free walk runs to the end; each hart's appended labels re-index its remaining
row with the failed acquires filtered out, `CertZ26.keepB`).

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ25

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

open Classical in
/-- A slot the walk realizes: no failed acquire. -/
noncomputable def CertZ26.keepB (L : Int → Prop) (l : Lbl) : Bool := !decide (CertZ24.lblFail L l)

theorem CertZ26.keepBTrue (L : Int → Prop) (l : Lbl) :
    CertZ26.keepB L l = true ↔ ¬ CertZ24.lblFail L l := by
  unfold CertZ26.keepB
  simp

/-- **THE WALK POLICY WITH SKIP STEPS.** -/
def CertZ26.walkPolZ4 (d0 : Efab) (rows : List (List Lbl)) (L : Int → Prop) (Inv : CertZ2.WInv) :
    Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (cnt : Nat → Nat),
    CertZ.cstOkZW d0 St itvOf fiOf → Inv St itvOf fiOf cnt →
    (∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length) →
    ∃ (x : Nat) (lb : Lbl), x < rows.length ∧ (rows.getD x [])[cnt x]? = some lb ∧
      ((CertZ24.lblFail L lb ∧ Inv St itvOf fiOf (CertZ2.bump cnt x)) ∨
       (¬ CertZ24.lblFail L lb ∧
        ∃ (lb' : Lbl) (pC pa : Pexv6) (da : Efab) (ls : List Wlabel) (pC' : Pexv6) (d' : Efab),
          (St.cstPst (cdEnd St.cstC))[x]? = some pC ∧
          lblReidxW lb lb' ∧ CertZ2.stepOkZ St itvOf x lb' pC pa da ls pC' d' ∧
          Inv (CertZ2.stSnoc St x lb' pC' d') (CertZ.itvSnoc St.cstC ⟨x, lb'⟩ ls itvOf fiOf)
            (CertZ.fiSnoc St.cstC ⟨x, lb'⟩ ls fiOf) (CertZ2.bump cnt x)))

/-- **`CertZ26.walkRunZ4` — THE FREE WALK WITH SKIPS.** -/
theorem CertZ26.walkRunZ4 (d0 : Efab) (rows : List (List Lbl)) (L : Int → Prop)
    (Inv : CertZ2.WInv) (hpol : CertZ26.walkPolZ4 d0 rows L Inv) :
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
        (∀ x, List.Forall₂ lblReidxW
          ((((rows.getD x []).drop (cnt x)).take (cntF x - cnt x)).filter (CertZ26.keepB L))
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
    · obtain ⟨x, lb, hx, hlb, hcase⟩ := hpol St itvOf fiOf cnt hok hinv hd
      have hcx : cnt x < (rows.getD x []).length := lookup_lt_Some hlb
      have hrem := CertZ2.remStep (fun x => (rows.getD x []).length) cnt x rows.length hx hcx
      rcases hcase with ⟨hfail, hinv1⟩ | ⟨hnf, lb', pC, pa, da, ls, pC', d', hp, hre,
          ⟨hmok, hld, hrun, hcut, harm⟩, hinv1⟩
      · -- a SKIP step
        obtain ⟨l, Sf, itvOf', fiOf', cntF, tradd, hrun', hokF, hinvF, hdone, hmono, htr, hf2,
          hagt, himg, hpst⟩ := ih St _ _ (CertZ2.bump cnt x) (by omega) hok hinv1
        have hmonoF : ∀ y, cnt y ≤ cntF y := by
          intro y
          have := hmono y
          by_cases hy : y = x
          · subst hy; rw [CertZ2.bumpSelf] at this; omega
          · rw [CertZ2.bumpNe cnt x y hy] at this; exact this
        refine ⟨l, Sf, itvOf', fiOf', cntF, tradd, hrun', hokF, hinvF, hdone, hmonoF, htr, ?_,
          hagt, himg, hpst⟩
        intro y
        have hfy := hf2 y
        by_cases hy : x = y
        · subst hy
          rw [CertZ2.bumpSelf] at hfy
          have hge : cnt x + 1 ≤ cntF x := by
            have := hmono x; rw [CertZ2.bumpSelf] at this; exact this
          rw [CertZ.dropCons _ (cnt x) lb hlb,
            show cntF x - cnt x = (cntF x - (cnt x + 1)) + 1 by omega, List.take_succ_cons,
            List.filter_cons_of_neg (by rw [CertZ26.keepBTrue]; exact fun h => h hfail)]
          exact hfy
        · rw [CertZ2.bumpNe cnt x y (Ne.symm hy)] at hfy
          exact hfy
      · -- a REALIZED step
        have hok1 := CertZ.cstOkZWSnoc d0 St itvOf fiOf x lb' pC pa da ls pC' d' hok hmok hld hp
          hrun hcut harm
        obtain ⟨l, Sf, itvOf', fiOf', cntF, tradd, hrun', hokF, hinvF, hdone, hmono, htr, hf2,
          hagt, himg, hpst⟩ := ih (CertZ2.stSnoc St x lb' pC' d') _ _ (CertZ2.bump cnt x)
            (by omega) hok1 hinv1
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
            rw [if_pos rfl]
            rw [CertZ2.bumpSelf] at hfy
            have hge : cnt x + 1 ≤ cntF x := by
              have := hmono x; rw [CertZ2.bumpSelf] at this; exact this
            rw [CertZ.dropCons _ (cnt x) lb hlb,
              show cntF x - cnt x = (cntF x - (cnt x + 1)) + 1 by omega, List.take_succ_cons,
              List.filter_cons_of_pos (by rw [CertZ26.keepBTrue]; exact hnf)]
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
