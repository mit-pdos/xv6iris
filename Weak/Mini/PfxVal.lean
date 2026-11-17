/-
Weak/Mini: **L5 MiniPfx — the cut's load values** (mini plan rev 4 §2 L5; Weak/Prom/PfxVal.lean's re-sourcing,
transcribed for the concrete mini harts).

Every load of the cut reads, in the cut, the gmo-latest of its candidates THAT ARE IN THE CUT (`csrc`); its value is
that store's value IN THE CUT'S RUN, so the values are a fixpoint `VC = FV VC`.  It exists by iteration
(`itV`): a load's value depends on the store it reads, whose value depends (taints are sound, PfxTaint.lean) only on
the loads of its data dependencies, which are gmo-before the load (rule 10, or rule 12 for a forwarded read), so of
lower rank; and every load of `Gl` keeps the execution's value (`good_itV`: its execution source is in the cut).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.PfxCut

namespace Weak.Mini.Pfx

open Weak.Mini Weak.Mini.Cmp

noncomputable section

open Classical

section defs

variable (P : MProg) (X : MExec) (O : List EvId)

/-- The memory operations of the cut. -/
def Dm : List EvId :=
  ndL (((List.range P.harts.length).flatMap (fun h => (List.range (cut P X O h)).map (fun i => (h, i)))).filter
    (fun e => decide ((X.evs P).isMem e)))

/-- The candidates of load `r` in the cut (rvwmo.adoc:316–324, the cut's stores only). -/
def candL (r : EvId) : List EvId :=
  (Dm P X O).filter (fun w => decide (((X.evs P).ev w).kind = .st ∧ ((X.evs P).ev w).pa = ((X.evs P).ev r).pa ∧
    ((X.evs P).gmo w r ∨ (X.evs P).po w r)))

/-- The element of largest rank. -/
def maxRk (A : MEvs) : List EvId → Option EvId
  | [] => none
  | x :: t => match maxRk A t with
    | none => some x
    | some y => if rk A y < rk A x then some x else some y

/-- THE STORE A LOAD OF THE CUT READS in the cut: its gmo-latest candidate in the cut. -/
def csrc (r : EvId) : Option EvId := maxRk (X.evs P) (candL P X O r)

/-- The value of event `w` in the cut-length run of its hart under load values `V`. -/
def evV (V : EvId → Nat) (w : EvId) : Nat := (((mrun P V w.1 (ksOf P X O w.1)).evs[w.2]?).getD default).v

/-- A load of the cut. -/
def isDLd (r : EvId) : Prop := inD P X O r ∧ ((X.evs P).ev r).kind = .ld

/-- One round: every load of the cut takes the value of the store it reads in the cut. -/
def FV (V : EvId → Nat) (r : EvId) : Nat :=
  if isDLd P X O r then
    (match csrc P X O r with
     | none => P.ini ((X.evs P).ev r).pa
     | some w => evV P X O V w)
  else X.V r

def itV : Nat → EvId → Nat
  | 0 => X.V
  | k + 1 => FV P X O (itV k)

/-- A bound on the ranks of the cut's memory operations. -/
def Rm : Nat := (Dm P X O).foldr (fun e m => max m (rk (X.evs P) e)) 0

/-- THE CUT'S LOAD VALUES. -/
def VC : EvId → Nat := itV P X O (Rm P X O + 1)

/-- `V` keeps the execution's values at the loads of `Gl` below the cut. -/
def Good (V : EvId → Nat) : Prop :=
  ∀ h i, BB P X O h i → V (h, i) % 2 ^ (8 * P.sz) = X.V (h, i) % 2 ^ (8 * P.sz)

end defs

theorem maxRk_none (A : MEvs) : ∀ (l : List EvId), maxRk A l = none → l = []
  | [], _ => rfl
  | x :: t, h => by
    simp only [maxRk] at h
    split at h
    · cases h
    · split at h <;> cases h

theorem maxRk_some (A : MEvs) : ∀ (l : List EvId) {y : EvId}, maxRk A l = some y →
    y ∈ l ∧ ∀ x ∈ l, rk A x ≤ rk A y
  | [], _, h => by cases h
  | x :: t, y, h => by
    simp only [maxRk] at h
    split at h
    · rename_i hn
      cases h
      have := maxRk_none A t hn; subst this
      simp
    · rename_i z hz
      obtain ⟨h1, h2⟩ := maxRk_some A t hz
      split at h
      · rename_i hlt
        cases h
        refine ⟨List.mem_cons_self, fun x' hx' => ?_⟩
        rcases List.mem_cons.1 hx' with rfl | hx'
        · exact Nat.le_refl _
        · have := h2 x' hx'; omega
      · rename_i hlt
        cases h
        refine ⟨List.mem_cons_of_mem _ h1, fun x' hx' => ?_⟩
        rcases List.mem_cons.1 hx' with rfl | hx'
        · omega
        · exact h2 x' hx'

section lemmas

variable {P : MProg} {X : MExec} {O : List EvId} (H : Hyp P X O)
include H

omit H in
theorem mem_Dm (e : EvId) : e ∈ Dm P X O ↔ inD P X O e ∧ (X.evs P).isMem e := by
  unfold Dm
  rw [mem_ndL, List.mem_filter, decide_eq_true_eq]
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨h, hh, i, hi, rfl⟩, hm⟩; exact ⟨⟨hh, hi⟩, hm⟩
  · rintro ⟨⟨hh, hi⟩, hm⟩; exact ⟨⟨e.1, hh, e.2, hi, rfl⟩, hm⟩

omit H in
theorem mem_candL (r w : EvId) : w ∈ candL P X O r ↔ inD P X O w ∧ (X.evs P).isMem w ∧
    ((X.evs P).ev w).kind = .st ∧ ((X.evs P).ev w).pa = ((X.evs P).ev r).pa ∧
      ((X.evs P).gmo w r ∨ (X.evs P).po w r) := by
  unfold candL
  rw [List.mem_filter, decide_eq_true_eq, mem_Dm, and_assoc]

/-- The cut's events are below the cut on their hart. -/
theorem inD_po {r w : EvId} (hr : inD P X O r) (hw : (X.evs P).has w) (hpo : (X.evs P).po w r) : inD P X O w := by
  obtain ⟨h, i⟩ := r; obtain ⟨h', j⟩ := w
  have : h' = h := hpo.1; subst this
  have := xidx hpo hw (inD_has H hr)
  have h2 := hr.2
  exact ⟨hr.1, show j < cut P X O h' by simp only at h2; omega⟩

theorem inD_Gst {w : EvId} (hw : w ∈ Gl P X O) (hs : ((X.evs P).ev w).kind = .st) : inD P X O w := by
  have hm := Gl_mem H hw
  refine ⟨hm.1.1, (lt_cutOf _ _ _).2 ⟨w, ?_, rfl, Nat.le_refl _⟩⟩
  unfold Al; exact List.mem_append_right _ (List.mem_filter.2 ⟨hw, decide_eq_true hs⟩)

/-- The source the cut gives a load: none means no candidate in the cut; otherwise the gmo-latest one. -/
theorem csrc_spec (r : EvId) :
    (csrc P X O r = none → ∀ w, w ∉ candL P X O r) ∧
    (∀ w, csrc P X O r = some w → w ∈ candL P X O r ∧ ∀ w' ∈ candL P X O r, w' = w ∨ (X.evs P).gmo w' w) := by
  refine ⟨fun h w hw => ?_, fun w h => ?_⟩
  · have := maxRk_none _ _ h; rw [this] at hw; cases hw
  · obtain ⟨h1, h2⟩ := maxRk_some _ _ h
    refine ⟨h1, fun w' hw' => ?_⟩
    have hm := ((mem_candL r w).1 h1).2.1
    have hm' := ((mem_candL r w').1 hw').2.1
    rcases Nat.lt_or_eq_of_le (h2 w' hw') with hlt | heq
    · exact .inr ((gmo_iff_rk (hg H) (hprog H) hm' hm).2 hlt)
    · exact .inl (rk_inj (hg H) (hprog H) hm' hm heq)

/-- The cut's candidates are the execution's candidates in the cut. -/
theorem candL_cand {r w : EvId} (hw : w ∈ candL P X O r) : (X.evs P).cand r w := by
  obtain ⟨_, hm, hs, hpa, ho⟩ := (mem_candL r w).1 hw
  exact ⟨hm.1, hs, hpa, ho⟩

theorem cand_candL {r w : EvId} (hr : inD P X O r) (hc : (X.evs P).cand r w)
    (hin : (X.evs P).gmo w r → w ∈ Gl P X O) : w ∈ candL P X O r := by
  obtain ⟨hw, hs, hpa, ho⟩ := hc
  refine (mem_candL r w).2 ⟨?_, ⟨hw, .inr hs⟩, hs, hpa, ho⟩
  rcases ho with ho | ho
  · exact inD_Gst H (hin ho) hs
  · exact inD_po H hr hw ho

/-! ## The runs under good values -/

theorem agree_good {V : EvId → Nat} (hV : Good P X O V) {h : Nat} (hh : h < P.harts.length) :
    Agree (BB P X O h) (mrun P X.V h (ksOf P X O h)) (mrun P V h (ksOf P X O h)) :=
  agree_run P (fun i hi => (hV h i hi).symm) _ (deps_G H hh).1 (deps_G H hh).2

/-- The cut-length runs under two good value maps that agree on `B' ⊇ BB` agree on `B'`. -/
theorem agree_two {V1 V2 : EvId → Nat} (h1 : Good P X O V1) {h : Nat} (hh : h < P.harts.length)
    {B' : Nat → Prop} (hB : ∀ i, BB P X O h i → B' i)
    (h12 : ∀ i, B' i → V1 (h, i) % 2 ^ (8 * P.sz) = V2 (h, i) % 2 ^ (8 * P.sz)) :
    Agree B' (mrun P V1 h (ksOf P X O h)) (mrun P V2 h (ksOf P X O h)) := by
  have hA := agree_good H h1 hh
  obtain ⟨hc, ha⟩ := deps_G H hh
  refine agree_run P h12 _ (fun x hx => hB x (hc x (by rw [hA.ctl]; exact hx))) (fun e he x hx => ?_)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hl : i < (mrun P X.V h (ksOf P X O h)).evs.length := by rw [hA.len]; exact hi
  have := congrArg (fun l => (l[i]?).map MEv.adep) hA.evs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hl, Option.map_some,
    noV, Option.some.injEq] at this
  exact hB x (ha _ (List.getElem_mem hl) x (by rw [this]; exact hx))

/-- A store's value in the run under `V`, when its data dependencies are in `B'`: as in the run under `V'`. -/
theorem evV_eq {V1 V2 : EvId → Nat} {B' : Nat → Prop} {w : EvId}
    (hA : Agree B' (mrun P V1 w.1 (ksOf P X O w.1)) (mrun P V2 w.1 (ksOf P X O w.1)))
    (hw : w.2 < (mrun P V1 w.1 (ksOf P X O w.1)).evs.length)
    (hs : (mrun P V1 w.1 (ksOf P X O w.1)).evs[w.2].kind = .st)
    (hd : ∀ d ∈ (mrun P V1 w.1 (ksOf P X O w.1)).evs[w.2].ddep, B' d) : evV P X O V1 w = evV P X O V2 w := by
  have hw2 : w.2 < (mrun P V2 w.1 (ksOf P X O w.1)).evs.length := by rw [← hA.len]; exact hw
  have := (hA.evV w.2 _ _ (List.getElem?_eq_getElem hw) (List.getElem?_eq_getElem hw2)).2.1 hs hd
  unfold evV; rw [List.getElem?_eq_getElem hw, List.getElem?_eq_getElem hw2]; exact this

/-- In the execution's run, a cut event is the execution's event. -/
theorem run_ev {w : EvId} (hw : inD P X O w) :
    ∃ hl : w.2 < (mrun P X.V w.1 (ksOf P X O w.1)).evs.length,
      (mrun P X.V w.1 (ksOf P X O w.1)).evs[w.2] = (X.evs P).ev w := by
  have hl : w.2 < (mrun P X.V w.1 (ksOf P X O w.1)).evs.length := by rw [(ksOf_spec H w.1).1]; exact hw.2
  exact ⟨hl, (xev hl).symm⟩

/-- The data dependencies of a store are loads of the cut below it. -/
theorem ddep_ld {w : EvId} (hw : inD P X O w) {d : Nat} (hd : d ∈ ((X.evs P).ev w).ddep) :
    d < w.2 ∧ isDLd P X O (w.1, d) ∧ (X.evs P).isMem (w.1, d) := by
  obtain ⟨hl, he⟩ := run_ev H hw
  have := (mrun_wf P X.V w.1 _).deps w.2 _ (List.getElem?_eq_getElem hl) d (.inr (.inl (by rw [he]; exact hd)))
  obtain ⟨hm, hld⟩ := xld hw.1 this.2
  have h2 := hw.2
  exact ⟨this.1, ⟨⟨hw.1, show d < cut P X O w.1 by omega⟩, hld⟩, hm⟩

/-- **The data dependencies of the store a cut load reads are gmo-before the load** (rule 10; rule 12 when the
load reads a po-earlier store of its hart). -/
theorem ddep_before {r w : EvId} (hr : isDLd P X O r) (hw : csrc P X O r = some w) {d : Nat}
    (hd : d ∈ ((X.evs P).ev w).ddep) : (X.evs P).gmo (w.1, d) r := by
  have hX := H.ex
  obtain ⟨hwc, hmax⟩ := (csrc_spec H r).2 w hw
  obtain ⟨hwD, hwm, hws, hwpa, hord⟩ := (mem_candL r w).1 hwc
  obtain ⟨hdl, _, hdm⟩ := ddep_ld H hwD hd
  have hrm : (X.evs P).isMem r := ⟨inD_has H hr.1, .inl hr.2⟩
  have hwh : w = (w.1, w.2) := rfl
  have h10 : (X.evs P).gmo (w.1, d) w :=
    ppoX hX hdm hwm (xpo hdl hwm.1) (.inr (.inr (.inr (.inr (.inl ⟨hws, rfl, hd⟩)))))
  rcases hord with hgw | hpo
  · exact MEvsF.gmo_trans (hg H) h10 hgw
  · obtain ⟨o, hrf, _⟩ := hX.2.2.2.1 r hrm.1 hr.2
    have hcw : (X.evs P).cand r w := ⟨hwm.1, hws, hwpa, .inr hpo⟩
    match o, hrf with
    | none, hrf => exact absurd hcw (hrf w)
    | some w0, hrf =>
      by_cases he : w0 = w
      · subst he
        exact ppoX hX hdm hrm ⟨(xpo hdl hwm.1).1.trans hpo.1, Nat.lt_trans (xpo hdl hwm.1).2 hpo.2⟩ (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨hr.2, w0, hwm.1, xpo hdl hwm.1, hpo, hws, .inr hd, hrf⟩)))))))
      · have hg0 : (X.evs P).gmo w w0 := by
          rcases hrf.2 w hcw with h | h
          · exact absurd h.symm he
          · exact h
        obtain ⟨hw0, hs0, hpa0, ho0⟩ := hrf.1
        by_cases hgr : (X.evs P).gmo w0 r
        · exact MEvsF.gmo_trans (hg H) (MEvsF.gmo_trans (hg H) h10 hg0) hgr
        · have ho0' : (X.evs P).po w0 r := ho0.resolve_left hgr
          have hc0 : w0 ∈ candL P X O r :=
            (mem_candL r w0).2 ⟨inD_po H hr.1 hw0 ho0', ⟨hw0, .inr hs0⟩, hs0, hpa0, .inr ho0'⟩
          rcases hmax w0 hc0 with h | h
          · exact absurd h he
          · exact absurd (MEvsF.gmo_asymm (hg H) h hg0) id

end lemmas

end

end Weak.Mini.Pfx
