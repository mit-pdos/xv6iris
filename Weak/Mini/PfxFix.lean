/-
Weak/Mini: **L5 MiniPfx — the cut's values are a fixpoint** (mini plan rev 4 §2 L5).

* `good_itV`: every round keeps the execution's values at the loads of `Gl` below the cut (their execution source
  is in the cut, and its value depends only on loads of `Gl`);
* `itV_stab`: a load's value is fixed from round `rk + 1` on (it depends on loads of lower rank);
* `VC_fix`: `VC` is a fixpoint at every load of the cut.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.PfxVal

namespace Weak.Mini.Pfx

open Weak.Mini Weak.Mini.Cmp

noncomputable section

open Classical

section lemmas

variable {P : MProg} {X : MExec} {O : List EvId} (H : Hyp P X O)
include H

/-- Under good values, a cut event is the execution's event up to its value. -/
theorem run_noV {V : EvId → Nat} (hV : Good P X O V) {w : EvId} (hw : inD P X O w) :
    ∃ hl : w.2 < (mrun P V w.1 (ksOf P X O w.1)).evs.length,
      noV ((mrun P V w.1 (ksOf P X O w.1)).evs[w.2]) = noV ((X.evs P).ev w) := by
  have hA := agree_good H hV hw.1
  obtain ⟨hl, he⟩ := run_ev H hw
  have hl' : w.2 < (mrun P V w.1 (ksOf P X O w.1)).evs.length := by rw [← hA.len]; exact hl
  refine ⟨hl', ?_⟩
  have := congrArg (fun l => l[w.2]?) hA.evs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hl', Option.map_some,
    Option.some.injEq] at this
  rw [← this, he]

theorem good_itV : ∀ k, Good P X O (itV P X O k)
  | 0 => fun _ _ _ => rfl
  | k + 1 => by
    intro h i hB
    have ih := good_itV k
    show FV P X O (itV P X O k) (h, i) % _ = _
    unfold FV
    split
    · rename_i hd
      have hrm := Gl_mem H hB.1
      obtain ⟨o, hrf, hval⟩ := H.ex.2.2.2.1 _ hrm.1 hd.2
      obtain ⟨hl, he⟩ := run_ev H hd.1
      have hv : ((X.evs P).ev (h, i)).v = X.V (h, i) % 2 ^ (8 * P.sz) := by
        rw [← he]; exact (mrun_new P X.V h _ i _ (List.getElem?_eq_getElem hl)).1 (by rw [he]; exact hd.2)
      cases o with
      | none =>
        have hc : csrc P X O (h, i) = none := by
          cases hc : csrc P X O (h, i) with
          | none => rfl
          | some w => exact absurd (candL_cand H ((csrc_spec H _).2 w hc).1) (hrf w)
        rw [hc]
        show P.ini _ % _ = _
        rw [← hv, hval]; simp only [MEvs.valOf, MProg.ini, Nat.mod_mod]
      | some w =>
        have hwc : w ∈ candL P X O (h, i) := cand_candL H hd.1 hrf.1 (fun hgm => Gl_down H hB.1 hgm)
        have hc : csrc P X O (h, i) = some w := by
          cases hc : csrc P X O (h, i) with
          | none => exact absurd hwc ((csrc_spec H _).1 hc w)
          | some w' =>
            obtain ⟨hw'c, hmax⟩ := (csrc_spec H _).2 w' hc
            rcases hmax w hwc with h1 | h1
            · rw [h1]
            · rcases hrf.2 w' (candL_cand H hw'c) with h2 | h2
              · rw [h2]
              · exact absurd (MEvsF.gmo_asymm (hg H) h1 h2) id
        rw [hc]
        show evV P X O (itV P X O k) w % _ = _
        have hwD := ((mem_candL _ w).1 hwc).1
        obtain ⟨hwl, hwe⟩ := run_ev H hwD
        have hA := agree_good H ih hwD.1
        have heq := evV_eq H (V1 := X.V) (V2 := itV P X O k) hA hwl
          (by rw [hwe]; exact ((mem_candL _ w).1 hwc).2.2.1)
          (by
            rw [hwe]; intro d hdd
            obtain ⟨hdl, _, _⟩ := ddep_ld H hwD hdd
            exact ⟨Gl_down H hB.1 (ddep_before H hd hc hdd), by have := hwD.2; omega⟩)
        rw [← heq]
        unfold evV; rw [List.getElem?_eq_getElem hwl]
        show (((mrun P X.V w.1 _).evs[w.2]).v) % _ = _
        rw [hwe, ← hv, hval]; simp only [MEvs.valOf]
        have hlt := mrun_v P X.V w.1 (ksOf P X O w.1) _ (List.getElem_mem hwl)
        rw [hwe] at hlt; exact Nat.mod_eq_of_lt hlt
    · rfl

theorem itV_stab (R : Nat) : ∀ r, isDLd P X O r → rk (X.evs P) r = R →
    ∀ m n, R < m → R < n → itV P X O m r = itV P X O n r := by
  induction R using Nat.strongRecOn with
  | ind R ih =>
    intro r hd hR m n hm hn
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    show FV P X O (itV P X O m') r = FV P X O (itV P X O n') r
    unfold FV
    rw [if_pos hd, if_pos hd]
    cases hc : csrc P X O r with
    | none => rfl
    | some w =>
      show evV P X O (itV P X O m') w = evV P X O (itV P X O n') w
      have hwD := ((mem_candL _ w).1 ((csrc_spec H r).2 w hc).1).1
      let B' : Nat → Prop := fun d => BB P X O w.1 d ∨ (isDLd P X O (w.1, d) ∧ rk (X.evs P) (w.1, d) < R)
      have hA := agree_two H (good_itV H m') hwD.1 (B' := B') (fun i hi => .inl hi) (fun d hd' => by
        rcases hd' with hb | ⟨hdd, hlt⟩
        · exact (good_itV H m' _ _ hb).trans (good_itV H n' _ _ hb).symm
        · rw [ih _ hlt (w.1, d) hdd rfl m' n' (by omega) (by omega)])
      obtain ⟨hl, hno⟩ := run_noV H (good_itV H m') hwD
      have hkd := congrArg MEv.kind hno
      have hdd := congrArg MEv.ddep hno
      simp only [noV] at hkd hdd
      refine evV_eq H hA hl ?_ ?_
      · rw [hkd]; exact ((mem_candL _ w).1 ((csrc_spec H r).2 w hc).1).2.2.1
      · rw [hdd]; intro d hd'
        obtain ⟨_, hdl, hdm⟩ := ddep_ld H hwD hd'
        refine .inr ⟨hdl, ?_⟩
        rw [← hR]; exact rk_lt (hg H) (hprog H) (ddep_before H hd hc hd')

omit H in
theorem le_foldr (A : MEvs) : ∀ (l : List EvId) {e : EvId}, e ∈ l → rk A e ≤ l.foldr (fun e m => max m (rk A e)) 0
  | [], _, he => by cases he
  | x :: t, e, he => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 he with rfl | h
    · omega
    · have := le_foldr A t h; omega

omit H in
theorem le_Rm {e : EvId} (he : e ∈ Dm P X O) : rk (X.evs P) e ≤ Rm P X O := le_foldr _ _ he

/-- **`VC` is a fixpoint at every load of the cut.** -/
theorem VC_fix {r : EvId} (hd : isDLd P X O r) : FV P X O (VC P X O) r = VC P X O r := by
  have hr : r ∈ Dm P X O := (mem_Dm r).2 ⟨hd.1, ⟨inD_has H hd.1, .inl hd.2⟩⟩
  have := le_Rm hr
  exact itV_stab H _ r hd rfl (Rm P X O + 2) (Rm P X O + 1) (by omega) (by omega)

end lemmas

end

end Weak.Mini.Pfx
