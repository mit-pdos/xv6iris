/-
Weak/Mini: **L5 MiniPfx — the cut is a finite execution** (mini plan rev 4 §2 L5).

`cutC P X O` = the harts stopped at `ksOf`, the load values `VC`, gmo = the cut's memory operations sorted by rank
(the execution's gmo restricted).  `cut_miniCut`: it satisfies the axiom block.  Preserved program order holds
because every rule of the cut is a rule of the execution, except rules 2 and 12, which read the CUT's `rf`: for
those the cut's source is the execution's or a store gmo-before it (`rule12_X`, `rule2_X`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.PfxFix

namespace Weak.Mini.Pfx

open Weak.Mini Weak.Mini.Cmp

noncomputable section

open Classical

/-- The cut's gmo: its memory operations in rank order. -/
def gC (P : MProg) (X : MExec) (O : List EvId) : List EvId :=
  (Dm P X O).mergeSort (fun a b => decide (rk (X.evs P) a ≤ rk (X.evs P) b))

/-- **THE CUT** of the infinite execution `X` at the observed events `O`. -/
def cutC (P : MProg) (X : MExec) (O : List EvId) : MCut := ⟨ksOf P X O, VC P X O, gC P X O⟩

section lemmas

variable {P : MProg} {X : MExec} {O : List EvId} (H : Hyp P X O)
include H

theorem c_noV {e : EvId} (he : inD P X O e) :
    noV (((cutC P X O).evs P).ev e) = noV ((X.evs P).ev e) ∧
      e.2 < ((cutC P X O).st P e.1).evs.length := by
  obtain ⟨hl, h⟩ := run_noV H (good_itV H _) he
  refine ⟨?_, hl⟩
  show noV (((mrun P (itV P X O (Rm P X O + 1)) e.1 (ksOf P X O e.1)).evs[e.2]?).getD default) = _
  rw [List.getElem?_eq_getElem hl]; exact h

theorem c_has (e : EvId) : ((cutC P X O).evs P).has e ↔ inD P X O e := by
  constructor
  · rintro ⟨h1, h2⟩
    have hA := agree_good H (good_itV H (Rm P X O + 1)) h1
    have := (ksOf_spec H e.1).1
    exact ⟨h1, by rw [← this, hA.len]; exact h2⟩
  · intro he; exact ⟨he.1, (c_noV H he).2⟩

theorem c_kind {e : EvId} (he : inD P X O e) : (((cutC P X O).evs P).ev e).kind = ((X.evs P).ev e).kind := by
  have := congrArg MEv.kind (c_noV H he).1; simpa [noV] using this
theorem c_pa {e : EvId} (he : inD P X O e) : (((cutC P X O).evs P).ev e).pa = ((X.evs P).ev e).pa := by
  have := congrArg MEv.pa (c_noV H he).1; simpa [noV] using this
theorem c_ii {e : EvId} (he : inD P X O e) : (((cutC P X O).evs P).ev e).ii = ((X.evs P).ev e).ii := by
  have := congrArg MEv.ii (c_noV H he).1; simpa [noV] using this
theorem c_adep {e : EvId} (he : inD P X O e) : (((cutC P X O).evs P).ev e).adep = ((X.evs P).ev e).adep := by
  have := congrArg MEv.adep (c_noV H he).1; simpa [noV] using this
theorem c_ddep {e : EvId} (he : inD P X O e) : (((cutC P X O).evs P).ev e).ddep = ((X.evs P).ev e).ddep := by
  have := congrArg MEv.ddep (c_noV H he).1; simpa [noV] using this
theorem c_cdep {e : EvId} (he : inD P X O e) : (((cutC P X O).evs P).ev e).cdep = ((X.evs P).ev e).cdep := by
  have := congrArg MEv.cdep (c_noV H he).1; simpa [noV] using this

theorem c_isMem (e : EvId) : ((cutC P X O).evs P).isMem e ↔ inD P X O e ∧ (X.evs P).isMem e := by
  constructor
  · rintro ⟨hh, hk⟩
    have he := (c_has H e).1 hh
    exact ⟨he, inD_has H he, by unfold MEvs.isLd MEvs.isSt at hk ⊢; rw [← c_kind H he]; exact hk⟩
  · rintro ⟨he, -, hk⟩
    exact ⟨(c_has H e).2 he, by unfold MEvs.isLd MEvs.isSt at hk ⊢; rw [c_kind H he]; exact hk⟩

theorem c_po {a b : EvId} (ha : inD P X O a) (hb : inD P X O b) :
    ((cutC P X O).evs P).po a b ↔ (X.evs P).po a b := by
  unfold MEvs.po; rw [c_ii H ha, c_ii H hb]

theorem gC_pairwise : (gC P X O).Pairwise (fun x y => rk (X.evs P) x < rk (X.evs P) y) := by
  have hnd : (gC P X O).Nodup := (List.mergeSort_perm _ _).nodup_iff.2 (nodup_ndL _)
  have hs := List.pairwise_mergeSort (le := fun a b => decide (rk (X.evs P) a ≤ rk (X.evs P) b))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) (Dm P X O)
  refine ((hs.and hnd).imp_of_mem (fun {x y} hx hy ⟨h1, h2⟩ => ?_))
  simp only [decide_eq_true_eq] at h1
  have hx' := ((mem_Dm x).1 (List.mem_mergeSort.1 hx)).2
  have hy' := ((mem_Dm y).1 (List.mem_mergeSort.1 hy)).2
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd (rk_inj (hg H) (hprog H) hx' hy' h) h2

theorem c_gmo (a b : EvId) : ((cutC P X O).evs P).gmo a b ↔ a ∈ Dm P X O ∧ b ∈ Dm P X O ∧ (X.evs P).gmo a b := by
  show a ∈ gC P X O ∧ b ∈ gC P X O ∧ posIn (gC P X O) a < posIn (gC P X O) b ↔ _
  constructor
  · rintro ⟨ha, hb, hp⟩
    have ha' := List.mem_mergeSort.1 ha
    have hb' := List.mem_mergeSort.1 hb
    refine ⟨ha', hb', (gmo_iff_rk (hg H) (hprog H) ((mem_Dm a).1 ha').2 ((mem_Dm b).1 hb').2).2 ?_⟩
    exact (posIn_lt_iff _ _ (gC_pairwise H) ha hb).1 hp
  · rintro ⟨ha, hb, hgm⟩
    have ha' : a ∈ gC P X O := List.mem_mergeSort.2 ha
    have hb' : b ∈ gC P X O := List.mem_mergeSort.2 hb
    exact ⟨ha', hb', (posIn_lt_iff _ _ (gC_pairwise H) ha' hb').2 (rk_lt (hg H) (hprog H) hgm)⟩

theorem c_gmoOk : ((cutC P X O).evs P).gmoOk := by
  refine ⟨fun a b h => ?_, fun a h => ?_, fun a b c h1 h2 => ?_, fun a b ha hb hne => ?_⟩
  · obtain ⟨ha, hb, _⟩ := (c_gmo H a b).1 h
    exact ⟨(c_isMem H a).2 ((mem_Dm a).1 ha), (c_isMem H b).2 ((mem_Dm b).1 hb)⟩
  · exact MEvsF.gmo_irr (hg H) a ((c_gmo H a a).1 h).2.2
  · obtain ⟨ha, _, h1⟩ := (c_gmo H a b).1 h1
    obtain ⟨_, hc, h2⟩ := (c_gmo H b c).1 h2
    exact (c_gmo H a c).2 ⟨ha, hc, MEvsF.gmo_trans (hg H) h1 h2⟩
  · have ha' := (c_isMem H a).1 ha
    have hb' := (c_isMem H b).1 hb
    rcases MEvsF.gmo_total (hg H) ha'.2 hb'.2 hne with h | h
    · exact .inl ((c_gmo H a b).2 ⟨(mem_Dm a).2 ha', (mem_Dm b).2 hb', h⟩)
    · exact .inr ((c_gmo H b a).2 ⟨(mem_Dm b).2 hb', (mem_Dm a).2 ha', h⟩)

/-- The cut's candidates of a cut load are `candL`. -/
theorem c_cand {r w : EvId} (hr : inD P X O r) : ((cutC P X O).evs P).cand r w ↔ w ∈ candL P X O r := by
  rw [mem_candL]
  constructor
  · rintro ⟨hw, hs, hpa, ho⟩
    have hw' := (c_has H w).1 hw
    have hs' : ((X.evs P).ev w).kind = .st := by rw [← c_kind H hw']; exact hs
    have hwm : (X.evs P).isMem w := ⟨inD_has H hw', .inr hs'⟩
    refine ⟨hw', hwm, hs', by rw [← c_pa H hw', ← c_pa H hr]; exact hpa, ?_⟩
    rcases ho with ho | ho
    · exact .inl ((c_gmo H w r).1 ho).2.2
    · exact .inr ((c_po H hw' hr).1 ho)
  · rintro ⟨hw', hwm, hs', hpa, ho⟩
    refine ⟨(c_has H w).2 hw', by unfold MEvs.isSt; rw [c_kind H hw']; exact hs',
      by rw [c_pa H hw', c_pa H hr]; exact hpa, ?_⟩
    rcases ho with ho | ho
    · have hrm : (X.evs P).isMem r := ((hg H).1 w r ho).2
      exact .inl ((c_gmo H w r).2 ⟨(mem_Dm w).2 ⟨hw', hwm⟩, (mem_Dm r).2 ⟨hr, hrm⟩, ho⟩)
    · exact .inr ((c_po H hw' hr).2 ho)

/-- The cut's `rf` of a cut load is `csrc`. -/
theorem c_rf {r : EvId} (hr : inD P X O r) : ((cutC P X O).evs P).rf r (csrc P X O r) := by
  cases hc : csrc P X O r with
  | none => exact fun w hw => (csrc_spec H r).1 hc w ((c_cand H hr).1 hw)
  | some w =>
    obtain ⟨hwc, hmax⟩ := (csrc_spec H r).2 w hc
    refine ⟨(c_cand H hr).2 hwc, fun w' hw' => ?_⟩
    rcases hmax w' ((c_cand H hr).1 hw') with h | h
    · exact .inl h
    · right
      have h1 := (mem_candL r w').1 ((c_cand H hr).1 hw')
      have h2 := (mem_candL r w).1 hwc
      exact (c_gmo H w' w).2 ⟨(mem_Dm w').2 ⟨h1.1, h1.2.1⟩, (mem_Dm w).2 ⟨h2.1, h2.2.1⟩, h⟩

theorem c_rf_eq {r : EvId} (hr : inD P X O r) {o : Option EvId} (ho : ((cutC P X O).evs P).rf r o) :
    o = csrc P X O r := MEvsF.rf_unique (c_gmoOk H) ho (c_rf H hr)

/-- Rule 12 of the cut is ordered by the execution's gmo. -/
theorem rule12_X {a b m : EvId} (ha : (X.evs P).isMem a) (hb : isDLd P X O b) (hm : inD P X O m)
    (h1 : (X.evs P).po a m) (h2 : (X.evs P).po m b) (hs : ((X.evs P).ev m).kind = .st)
    (hd : a.2 ∈ ((X.evs P).ev m).adep ∨ a.2 ∈ ((X.evs P).ev m).ddep) (hc : csrc P X O b = some m) :
    (X.evs P).gmo a b := by
  have hX := H.ex
  have hmm : (X.evs P).isMem m := ⟨inD_has H hm, .inr hs⟩
  have hbm : (X.evs P).isMem b := ⟨inD_has H hb.1, .inl hb.2⟩
  have hpa : ((X.evs P).ev m).pa = ((X.evs P).ev b).pa :=
    ((mem_candL b m).1 ((csrc_spec H b).2 m hc).1).2.2.2.1
  have ham : (X.evs P).gmo a m := by
    rcases hd with hd | hd
    · exact ppoX hX ha hmm h1 (.inr (.inr (.inr (.inl ⟨h1.1, hd⟩))))
    · exact ppoX hX ha hmm h1 (.inr (.inr (.inr (.inr (.inl ⟨hs, h1.1, hd⟩)))))
  have hpo : (X.evs P).po a b := ⟨h1.1.trans h2.1, Nat.lt_trans h1.2 h2.2⟩
  obtain ⟨o, hrf, _⟩ := hX.2.2.2.1 b hbm.1 hb.2
  have hcm : (X.evs P).cand b m := ⟨hmm.1, hs, hpa, .inr h2⟩
  match o, hrf with
  | none, hrf => exact absurd hcm (hrf m)
  | some w0, hrf =>
    by_cases he : w0 = m
    · subst he
      exact ppoX hX ha hbm hpo (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hb.2, w0, hmm.1, h1, h2, hs, hd, hrf⟩)))))))
    · have hg0 : (X.evs P).gmo m w0 := (hrf.2 m hcm).resolve_left (Ne.symm he)
      obtain ⟨hw0, hs0, hpa0, ho0⟩ := hrf.1
      by_cases hgr : (X.evs P).gmo w0 b
      · exact MEvsF.gmo_trans (hg H) (MEvsF.gmo_trans (hg H) ham hg0) hgr
      · have ho0' := ho0.resolve_left hgr
        have hc0 : w0 ∈ candL P X O b :=
          (mem_candL b w0).2 ⟨inD_po H hb.1 hw0 ho0', ⟨hw0, .inr hs0⟩, hs0, hpa0, .inr ho0'⟩
        rcases ((csrc_spec H b).2 m hc).2 w0 hc0 with h | h
        · exact absurd h he
        · exact absurd (MEvsF.gmo_asymm (hg H) h hg0) id

/-- Rule 2 of the cut is ordered by the execution's gmo. -/
theorem rule2_X {a b : EvId} (ha : isDLd P X O a) (hb : isDLd P X O b) (hpo : (X.evs P).po a b)
    (hpa : ((X.evs P).ev a).pa = ((X.evs P).ev b).pa)
    (hno : ∀ m, (X.evs P).has m → (X.evs P).po a m → (X.evs P).po m b →
      ¬ ((X.evs P).isSt m ∧ ((X.evs P).ev m).pa = ((X.evs P).ev a).pa))
    (hne : csrc P X O a ≠ csrc P X O b) : (X.evs P).gmo a b := by
  have hX := H.ex
  have hG := hg H
  have ham : (X.evs P).isMem a := ⟨inD_has H ha.1, .inl ha.2⟩
  have hbm : (X.evs P).isMem b := ⟨inD_has H hb.1, .inl hb.2⟩
  apply Classical.byContradiction
  intro hab
  have hab' : a ≠ b := fun h => by subst h; exact Nat.lt_irrefl _ hpo.2
  have hba : (X.evs P).gmo b a := (MEvsF.gmo_total hG ham hbm hab').resolve_left hab
  obtain ⟨oa, hra, _⟩ := hX.2.2.2.1 a ham.1 ha.2
  obtain ⟨ob, hrb, _⟩ := hX.2.2.2.1 b hbm.1 hb.2
  have hoe : oa = ob := by
    apply Classical.byContradiction; intro h
    exact hab (ppoX hX ham hbm hpo (.inr (.inl ⟨ha.2, hb.2, hpa, hno, oa, ob, hra, hrb, h⟩)))
  subst hoe
  -- a candidate of `b` in the cut is one of `a`
  have hsub : ∀ w ∈ candL P X O b, w ∈ candL P X O a := by
    intro w hw
    obtain ⟨hwD, hwm, hws, hwpa, ho⟩ := (mem_candL b w).1 hw
    refine (mem_candL a w).2 ⟨hwD, hwm, hws, hwpa.trans hpa.symm, ?_⟩
    rcases ho with ho | ho
    · exact .inl (MEvsF.gmo_trans hG ho hba)
    · right
      obtain ⟨h0, j⟩ := w; obtain ⟨h1, i⟩ := a; obtain ⟨h2, k⟩ := b
      have e1 : h0 = h2 := ho.1; have e2 : h1 = h2 := hpo.1; subst e1; subst e2
      rcases Nat.lt_trichotomy j i with hlt | heq | hgt
      · exact xpo hlt (inD_has H ha.1)
      · subst heq; exact absurd hws (by rw [ha.2]; intro h; cases h)
      · exact absurd ⟨hws, hwpa.trans hpa.symm⟩ (hno _ hwm.1 (xpo hgt hwm.1) ho)
  -- a cut candidate of `a` that is not one of `b` is gmo-below every candidate of `b` reading `a`'s source
  have hextra : ∀ w ∈ candL P X O a, w ∉ candL P X O b →
      ∃ w0 ∈ candL P X O b, (X.evs P).gmo w w0 := by
    intro w hw hnb
    obtain ⟨hwD, hwm, hws, hwpa, ho⟩ := (mem_candL a w).1 hw
    have hpob : ¬ (X.evs P).po w b := fun h =>
      hnb ((mem_candL b w).2 ⟨hwD, hwm, hws, hwpa.trans hpa, .inr h⟩)
    have hgw : (X.evs P).gmo w a := ho.resolve_right (fun h => hpob ⟨h.1.trans hpo.1, Nat.lt_trans h.2 hpo.2⟩)
    have hgb : ¬ (X.evs P).gmo w b := fun h =>
      hnb ((mem_candL b w).2 ⟨hwD, hwm, hws, hwpa.trans hpa, .inl h⟩)
    have hbw : (X.evs P).gmo b w := (MEvsF.gmo_total hG hbm hwm (fun h => by
      subst h; exact absurd hws (by rw [hb.2]; intro h; cases h))).resolve_right hgb
    have hca : (X.evs P).cand a w := ⟨hwm.1, hws, hwpa, .inl hgw⟩
    match oa, hra, hrb with
    | none, hra, _ => exact absurd hca (hra w)
    | some w0, hra, hrb =>
      have hw0 : w = w0 ∨ (X.evs P).gmo w w0 := hra.2 w hca
      obtain ⟨hw0h, hs0, hpa0, ho0⟩ := hrb.1
      have hgb0 : ¬ (X.evs P).gmo w0 b := fun h => by
        rcases hw0 with rfl | hw0
        · exact MEvsF.gmo_asymm hG hbw h
        · exact MEvsF.gmo_asymm hG (MEvsF.gmo_trans hG hbw hw0) h
      have ho0' := ho0.resolve_left hgb0
      have hc0 : w0 ∈ candL P X O b :=
        (mem_candL b w0).2 ⟨inD_po H hb.1 hw0h ho0', ⟨hw0h, .inr hs0⟩, hs0, hpa0, .inr ho0'⟩
      rcases hw0 with rfl | hw0
      · exact absurd hc0 hnb
      · exact ⟨w0, hc0, hw0⟩
  apply hne
  cases hcb : csrc P X O b with
  | none =>
    cases hca : csrc P X O a with
    | none => rfl
    | some w =>
      have hw := ((csrc_spec H a).2 w hca).1
      have hnb : w ∉ candL P X O b := (csrc_spec H b).1 hcb w
      obtain ⟨w0, hc0, _⟩ := hextra w hw hnb
      exact absurd hc0 ((csrc_spec H b).1 hcb w0)
  | some wb =>
    obtain ⟨hwbc, hmaxb⟩ := (csrc_spec H b).2 wb hcb
    cases hca : csrc P X O a with
    | none => exact absurd (hsub wb hwbc) ((csrc_spec H a).1 hca wb)
    | some wa =>
      obtain ⟨hwac, hmaxa⟩ := (csrc_spec H a).2 wa hca
      rcases hmaxa wb (hsub wb hwbc) with h | h
      · rw [h]
      · exfalso
        by_cases hin : wa ∈ candL P X O b
        · rcases hmaxb wa hin with h' | h'
          · subst h'; exact MEvsF.gmo_irr hG _ h
          · exact MEvsF.gmo_asymm hG h h'
        · obtain ⟨w0, hc0, hg0⟩ := hextra wa hwac hin
          rcases hmaxb w0 hc0 with h' | h'
          · subst h'; exact MEvsF.gmo_asymm hG h hg0
          · exact MEvsF.gmo_asymm hG h (MEvsF.gmo_trans hG hg0 h')

end lemmas

end

end Weak.Mini.Pfx
