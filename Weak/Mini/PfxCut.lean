/-
Weak/Mini: **L5 MiniPfx — the cut of an infinite execution** (mini plan rev 4 §2 L5; the full development's
Weak/Prom/PfxCut.lean, transcribed for the concrete mini harts, not imported).

Given an infinite execution `X` of `P` (`miniExec`) and a finite list `O` of its memory operations:
* `Pl` = po-down(O); `Ml` its memory operations; `Gl` their gmo-down-closure (FINITE by progress, PfxRank.lean);
* the ANCHORS `Al` = `O` and the stores of `Gl`; `cut h` = one past hart `h`'s last anchor; `ksOf h` = the first
  step at which hart `h` has emitted `cut h` events (so its last step emitted the last anchor);
* `deps_G` — THE KEY BOUND: every control taint and every address dependency of the hart up to its cut is a load
  of `Gl`: below an observed anchor it is in po-down(O); below a store anchor `z` it is ordered before `z` by rule 11
  (control: `z`'s control dependencies are the hart's control taint), rule 9 (`z`'s own address) or rule 13 (an
  address dependency of an earlier memory operation), rvwmo.adoc:293–302.
WHY NOT the po-down + gmo-down closure of O: it can be INFINITE (a load po-before a store of the closure may be
gmo-after it and read a store whose po-prefix has such a load again, …); so the cut keeps the path and the
addresses (`deps_G` + PfxTaint.lean) but RE-SOURCES the "late" loads (PfxVal.lean), as Weak/Prom/PfxVal.lean does.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.PfxRank
import Weak.Mini.PfxTaint

namespace Weak.Mini.Pfx

open Weak.Mini Weak.Mini.Cmp

noncomputable section

open Classical

/-! ## 1. More hart-run facts -/

theorem exec_ctl_emit (sz h : Nat) (V : EvId → Nat) (s : Weak.Mini.MSt) (i : MI)
    (hl : (exec sz h V s i).evs.length = s.evs.length + 1) : (exec sz h V s i).ctl = s.ctl := by
  cases i with
  | alui op rd rs1 imm =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; simp [exec, h1, MSt.adv, (wr_same _ _ _).2.1] at hl
  | alu op rd rs1 rs2 =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩
    simp [exec, h1, h2, MSt.adv, (wr_same _ _ _).2.1] at hl
  | load sgn rd rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; simp [exec, h1, MSt.adv, (wr_same _ _ _).2.2.2, MSt.emit]
  | store rs2 rs1 off =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩; simp [exec, h1, h2, MSt.adv, MSt.emit]
  | fence f => simp [exec, MSt.adv, MSt.emit]
  | br c rs1 rs2 tgt =>
    rcases h1 : s.rd rs1 with ⟨v1, t1⟩; rcases h2 : s.rd rs2 with ⟨v2, t2⟩; simp [exec, h1, h2] at hl
  | jmp tgt => simp [exec] at hl
  | nop => simp [exec, MSt.adv] at hl

theorem mstep_ctl_emit (P : MProg) (V : EvId → Nat) (h : Nat) (s : Weak.Mini.MSt)
    (hl : (mstep P V h s).evs.length = s.evs.length + 1) : (mstep P V h s).ctl = s.ctl := by
  unfold mstep at hl ⊢; split at hl
  · exact exec_ctl_emit _ _ _ _ _ hl
  · omega

/-- The new event of a step: a load's value is the execution's value for it (its `sz` bytes); a fence has no
address dependency. -/
theorem exec_new (sz h : Nat) (V : EvId → Nat) (s : Weak.Mini.MSt) (i : MI) :
    ∀ j e, (exec sz h V s i).evs[j]? = some e → s.evs[j]? = some e ∨
      ((e.kind = .ld → e.v = V (h, j) % 2 ^ (8 * sz)) ∧ (∀ f, e.kind = .fence f → e.adep = [])) := by
  intro j e he
  rcases exec_evs sz h V s i with h1 | ⟨e', h1, _⟩
  · rw [h1] at he; exact .inl he
  · rw [h1] at he
    rcases Nat.lt_or_ge j s.evs.length with hj | hj
    · rw [List.getElem?_append_left hj] at he; exact .inl he
    · right
      rw [List.getElem?_append_right hj] at he
      have hj0 : j - s.evs.length = 0 := by
        rcases Nat.eq_zero_or_pos (j - s.evs.length) with h0 | h0
        · exact h0
        · rw [List.getElem?_eq_none (by simp; omega)] at he; cases he
      rw [hj0] at he; simp at he; subst he
      have hjl : j = s.evs.length := by omega
      subst hjl
      cases i with
      | load sgn rd rs1 off =>
        rcases h2 : s.rd rs1 with ⟨v1, t1⟩
        simp [exec, h2, MSt.adv, (wr_same _ _ _).2.1, MSt.emit] at h1; rw [← h1]
        exact ⟨fun _ => rfl, fun _ hh => (by cases hh)⟩
      | store rs2 rs1 off =>
        rcases h2 : s.rd rs1 with ⟨v1, t1⟩; rcases h3 : s.rd rs2 with ⟨v2, t2⟩
        simp [exec, h2, h3, MSt.adv, MSt.emit] at h1; rw [← h1]
        exact ⟨fun hh => (by cases hh), fun _ hh => (by cases hh)⟩
      | fence f =>
        simp [exec, MSt.adv, MSt.emit] at h1; rw [← h1]
        exact ⟨fun hh => (by cases hh), fun _ _ => rfl⟩
      | alui op rd rs1 imm =>
        rcases h2 : s.rd rs1 with ⟨v1, t1⟩; simp [exec, h2, MSt.adv, (wr_same _ _ _).2.1] at h1
      | alu op rd rs1 rs2 =>
        rcases h2 : s.rd rs1 with ⟨v1, t1⟩; rcases h3 : s.rd rs2 with ⟨v2, t2⟩
        simp [exec, h2, h3, MSt.adv, (wr_same _ _ _).2.1] at h1
      | br c rs1 rs2 tgt =>
        rcases h2 : s.rd rs1 with ⟨v1, t1⟩; rcases h3 : s.rd rs2 with ⟨v2, t2⟩; simp [exec, h2, h3] at h1
      | jmp tgt => simp [exec] at h1
      | nop => simp [exec, MSt.adv] at h1

theorem mrun_new (P : MProg) (V : EvId → Nat) (h : Nat) :
    ∀ k j e, (mrun P V h k).evs[j]? = some e →
      (e.kind = .ld → e.v = V (h, j) % 2 ^ (8 * P.sz)) ∧ (∀ f, e.kind = .fence f → e.adep = [])
  | 0, j, e, he => by simp [mrun, MProg.init] at he
  | k + 1, j, e, he => by
    change (mstep P V h (mrun P V h k)).evs[j]? = some e at he
    unfold mstep at he; split at he
    · rcases exec_new _ _ _ _ _ j e he with h1 | h1
      · exact mrun_new P V h k j e h1
      · exact h1
    · exact mrun_new P V h k j e he

/-- Every count of events up to the current one is reached, at a first step. -/
theorem exists_len (P : MProg) (V : EvId → Nat) (h : Nat) : ∀ K n, n ≤ (mrun P V h K).evs.length →
    ∃ k, (mrun P V h k).evs.length = n ∧ ∀ k' < k, (mrun P V h k').evs.length < n
  | 0, n, hn => ⟨0, by simp [mrun, MProg.init] at hn ⊢; omega, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | K + 1, n, hn => by
    by_cases h1 : n ≤ (mrun P V h K).evs.length
    · exact exists_len P V h K n h1
    · have h2 := mrun_len_succ P V h K
      refine ⟨K + 1, by omega, fun k' hk' => ?_⟩
      have := (mrun_mono P V h (show k' ≤ K by omega)).length_le
      omega

/-! ## 2. The execution's events -/

section xfacts

variable {P : MProg} {X : MExec}

theorem mrun_get (P : MProg) (V : EvId → Nat) (h i : Nat) {k k' : Nat} (hk : i < (mrun P V h k).evs.length)
    (hk' : i < (mrun P V h k').evs.length) : (mrun P V h k).evs[i] = (mrun P V h k').evs[i] := by
  have h1 := mrun_mono P V h (Nat.le_max_left k k')
  have h2 := mrun_mono P V h (Nat.le_max_right k k')
  rw [h1.getElem hk, h2.getElem hk']

theorem xev {e : EvId} {k : Nat} (hk : e.2 < (mrun P X.V e.1 k).evs.length) :
    (X.evs P).ev e = (mrun P X.V e.1 k).evs[e.2] := by
  show X.ev P e = _
  unfold MExec.ev
  rw [dif_pos ⟨k, hk⟩]
  exact mrun_get P X.V e.1 e.2 _ _

theorem xev_of {h i k : Nat} {e : MEv} (hj : (mrun P X.V h k).evs[i]? = some e) : (X.evs P).ev (h, i) = e := by
  rw [xev (k := k) (List.getElem?_eq_some_iff.1 hj).1]; exact (List.getElem?_eq_some_iff.1 hj).2

theorem xhas_le {h i j : Nat} (hj : (X.evs P).has (h, j)) (hij : i ≤ j) : (X.evs P).has (h, i) :=
  ⟨hj.1, by obtain ⟨k, hk⟩ := hj.2; exact ⟨k, by simp only at hk ⊢; omega⟩⟩

theorem xpo {h i j : Nat} (hij : i < j) (hj : (X.evs P).has (h, j)) : (X.evs P).po (h, i) (h, j) := by
  obtain ⟨k, hk⟩ := hj.2
  simp only at hk
  refine ⟨rfl, ?_⟩
  rw [xev (k := k) (show i < _ by simp only; omega), xev (k := k) hk]
  exact List.pairwise_iff_getElem.1 (mrun_wf P X.V h k).ii_mono i j (by omega) hk hij

theorem xidx {h i j : Nat} (hpo : (X.evs P).po (h, i) (h, j)) (hi : (X.evs P).has (h, i))
    (hj : (X.evs P).has (h, j)) : i < j := by
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · exact h1
  · subst h1; exact absurd hpo.2 (Nat.lt_irrefl _)
  · exact absurd hpo.2 (Nat.lt_asymm (xpo h1 hi).2)

/-- A taint of a hart state names a load of the execution. -/
theorem xld {h k j : Nat} (hh : h < P.harts.length) (hl : ldAt (mrun P X.V h k).evs j) :
    (X.evs P).isMem (h, j) ∧ (X.evs P).isLd (h, j) := by
  obtain ⟨e, he, hkd⟩ := hl
  have hj := (List.getElem?_eq_some_iff.1 he).1
  have hev : (X.evs P).ev (h, j) = e := by
    rw [xev (k := k) hj]; exact (List.getElem?_eq_some_iff.1 he).2
  exact ⟨⟨⟨hh, k, hj⟩, .inl (by unfold MEvs.isLd; rw [hev]; exact hkd)⟩, by unfold MEvs.isLd; rw [hev]; exact hkd⟩

theorem ppoX (hX : miniExec P X) {a b : EvId} (ha : (X.evs P).isMem a) (hb : (X.evs P).isMem b)
    (hpo : (X.evs P).po a b)
    (hr : (X.evs P).rule1 a b ∨ (X.evs P).rule2 a b ∨ (X.evs P).rule4 a b ∨ (X.evs P).rule9 a b ∨
      (X.evs P).rule10 a b ∨ (X.evs P).rule11 a b ∨ (X.evs P).rule12 a b ∨ (X.evs P).rule13 a b) :
    (X.evs P).gmo a b := hX.2.2.1 a b ⟨ha, hb, hpo, hr⟩

end xfacts

/-! ## 3. The cut -/

section defs

variable (P : MProg) (X : MExec) (O : List EvId)

/-- po-down(O). -/
def Pl : List EvId := O.flatMap (fun o => (List.range (o.2 + 1)).map (fun i => (o.1, i)))

/-- Its memory operations. -/
def Ml : List EvId := (Pl O).filter (fun e => decide ((X.evs P).isMem e))

/-- Their gmo-down-closure. -/
def Gl : List EvId := (Ml P X O).flatMap (fun m => m :: preds (X.evs P) m)

/-- THE ANCHORS: the observed events and the stores of `Gl`. -/
def Al : List EvId := O ++ (Gl P X O).filter (fun e => decide (((X.evs P).ev e).kind = .st))

/-- One past the last element of `A` on hart `h`. -/
def cutOf (A : List EvId) (h : Nat) : Nat := A.foldr (fun z c => if z.1 = h then max c (z.2 + 1) else c) 0

/-- THE CUT of hart `h`: one past its last anchor. -/
def cut (h : Nat) : Nat := cutOf (Al P X O) h

/-- The first step at which hart `h` has emitted `cut h` events. -/
def ksOf (h : Nat) : Nat :=
  if hk : ∃ k, (mrun P X.V h k).evs.length = cut P X O h ∧ ∀ k' < k, (mrun P X.V h k').evs.length < cut P X O h
  then Classical.choose hk else 0

/-- An event of the cut. -/
def inD (e : EvId) : Prop := e.1 < P.harts.length ∧ e.2 < cut P X O e.1

/-- The loads whose values the cut keeps: those of `Gl` below the cut. -/
def BB (h i : Nat) : Prop := (h, i) ∈ Gl P X O ∧ i < cut P X O h

end defs

/-- The hypotheses: an infinite execution and observed memory operations. -/
structure Hyp (P : MProg) (X : MExec) (O : List EvId) : Prop where
  ex : miniExec P X
  obs : ∀ e ∈ O, (X.evs P).isMem e

theorem lt_cutOf (A : List EvId) (h i : Nat) : i < cutOf A h ↔ ∃ z ∈ A, z.1 = h ∧ i ≤ z.2 := by
  induction A with
  | nil => simp [cutOf]
  | cons z A ih =>
    unfold cutOf at ih ⊢
    simp only [List.foldr_cons, List.mem_cons]
    split
    · rename_i hz
      rw [show ∀ a b : Nat, i < max a b ↔ i < a ∨ i < b from fun a b => by omega, ih]
      constructor
      · rintro (⟨w, hw, h1, h2⟩ | h1)
        · exact ⟨w, Or.inr hw, h1, h2⟩
        · exact ⟨z, Or.inl rfl, hz, by omega⟩
      · rintro ⟨w, rfl | hw, h1, h2⟩
        · right; omega
        · left; exact ⟨w, hw, h1, h2⟩
    · rename_i hz
      rw [ih]
      constructor
      · rintro ⟨w, hw, h1, h2⟩; exact ⟨w, Or.inr hw, h1, h2⟩
      · rintro ⟨w, rfl | hw, h1, h2⟩
        · exact absurd h1 hz
        · exact ⟨w, hw, h1, h2⟩

theorem cutOf_max (A : List EvId) (h : Nat) (hp : 0 < cutOf A h) : ∃ z ∈ A, z.1 = h ∧ z.2 + 1 = cutOf A h := by
  induction A with
  | nil => simp [cutOf] at hp
  | cons z A ih =>
    unfold cutOf at ih hp ⊢
    simp only [List.foldr_cons, List.mem_cons] at hp ⊢
    split
    · rename_i hz
      rw [if_pos hz] at hp
      rcases Nat.le_total (A.foldr (fun z c => if z.1 = h then max c (z.2 + 1) else c) 0) (z.2 + 1) with h1 | h1
      · exact ⟨z, Or.inl rfl, hz, by rw [Nat.max_eq_right h1]⟩
      · rw [Nat.max_eq_left h1]
        obtain ⟨w, hw, h2, h3⟩ := ih (by omega)
        exact ⟨w, Or.inr hw, h2, h3⟩
    · rename_i hz
      rw [if_neg hz] at hp
      obtain ⟨w, hw, h2, h3⟩ := ih hp
      exact ⟨w, Or.inr hw, h2, h3⟩

section lemmas

variable {P : MProg} {X : MExec} {O : List EvId} (H : Hyp P X O)
include H

theorem hg : (X.evs P).gmoOk := H.ex.2.1
theorem hprog : (X.evs P).progressAx := H.ex.2.2.2.2

omit H in
theorem mem_Pl (e : EvId) : e ∈ Pl O ↔ ∃ o ∈ O, e.1 = o.1 ∧ e.2 ≤ o.2 := by
  unfold Pl
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨o, ho, i, hi, rfl⟩; exact ⟨o, ho, rfl, by simp only; omega⟩
  · rintro ⟨o, ho, h1, h2⟩; exact ⟨o, ho, e.2, by omega, by rw [← h1]⟩

omit H in
theorem mem_Ml (e : EvId) : e ∈ Ml P X O ↔ e ∈ Pl O ∧ (X.evs P).isMem e := by
  unfold Ml; rw [List.mem_filter, decide_eq_true_eq]

theorem mem_Gl (e : EvId) : e ∈ Gl P X O ↔ ∃ m ∈ Ml P X O, e = m ∨ (X.evs P).gmo e m := by
  unfold Gl
  simp only [List.mem_flatMap, List.mem_cons]
  constructor
  · rintro ⟨m, hm, h | h⟩
    · exact ⟨m, hm, .inl h⟩
    · exact ⟨m, hm, .inr ((mem_preds (hprog H) ((mem_Ml m).1 hm).2 e).1 h)⟩
  · rintro ⟨m, hm, h | h⟩
    · exact ⟨m, hm, .inl h⟩
    · exact ⟨m, hm, .inr ((mem_preds (hprog H) ((mem_Ml m).1 hm).2 e).2 h)⟩

theorem Gl_mem {e : EvId} (he : e ∈ Gl P X O) : (X.evs P).isMem e := by
  obtain ⟨m, hm, h | h⟩ := (mem_Gl H e).1 he
  · subst h; exact ((mem_Ml e).1 hm).2
  · exact ((hg H).1 e m h).1

theorem Gl_down {e e' : EvId} (he : e ∈ Gl P X O) (h : (X.evs P).gmo e' e) : e' ∈ Gl P X O := by
  obtain ⟨m, hm, h1 | h1⟩ := (mem_Gl H e).1 he
  · subst h1; exact (mem_Gl H e').2 ⟨e, hm, .inr h⟩
  · exact (mem_Gl H e').2 ⟨m, hm, .inr (MEvsF.gmo_trans (hg H) h h1)⟩

theorem Pl_Gl {e : EvId} (hp : e ∈ Pl O) (hm : (X.evs P).isMem e) : e ∈ Gl P X O :=
  (mem_Gl H e).2 ⟨e, (mem_Ml e).2 ⟨hp, hm⟩, .inl rfl⟩

theorem O_Gl {o : EvId} (ho : o ∈ O) : o ∈ Gl P X O :=
  Pl_Gl H ((mem_Pl o).2 ⟨o, ho, rfl, Nat.le_refl _⟩) (H.obs o ho)

theorem Al_mem {z : EvId} (hz : z ∈ Al P X O) :
    (X.evs P).isMem z ∧ (z ∈ O ∨ (z ∈ Gl P X O ∧ (X.evs P).isSt z)) := by
  unfold Al at hz
  rcases List.mem_append.1 hz with hz | hz
  · exact ⟨H.obs z hz, .inl hz⟩
  · rw [List.mem_filter, decide_eq_true_eq] at hz
    exact ⟨Gl_mem H hz.1, .inr ⟨hz.1, hz.2⟩⟩

/-- Below the cut, below an anchor. -/
theorem anchor_of {h i : Nat} (hi : i < cut P X O h) : ∃ z ∈ Al P X O, z.1 = h ∧ i ≤ z.2 :=
  (lt_cutOf _ h i).1 hi

theorem inD_has {e : EvId} (he : inD P X O e) : (X.evs P).has e := by
  obtain ⟨z, hz, h1, h2⟩ := anchor_of H he.2
  have := (Al_mem H hz).1.1
  obtain ⟨h0, i⟩ := e
  simp only at h1 h2
  obtain ⟨h3, i3⟩ := z
  simp only at h1 h2; subst h1
  exact xhas_le this h2

/-- The first step with `cut h` events. -/
theorem ksOf_spec (h : Nat) : (mrun P X.V h (ksOf P X O h)).evs.length = cut P X O h ∧
    ∀ k' < ksOf P X O h, (mrun P X.V h k').evs.length < cut P X O h := by
  have hex : ∃ k, (mrun P X.V h k).evs.length = cut P X O h ∧
      ∀ k' < k, (mrun P X.V h k').evs.length < cut P X O h := by
    by_cases h0 : cut P X O h = 0
    · exact ⟨0, by rw [h0]; rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · obtain ⟨z, hz, h1, h2⟩ := cutOf_max _ h (Nat.pos_of_ne_zero h0)
      obtain ⟨_, k, hk⟩ := (Al_mem H hz).1.1
      exact exists_len P X.V h k _ (by rw [h1] at hk; unfold cut; omega)
  unfold ksOf; rw [dif_pos hex]; exact Classical.choose_spec hex

/-- **THE KEY BOUND**: the hart's control taint and its events' address dependencies are loads of `Gl`. -/
theorem deps_G {h : Nat} (hh : h < P.harts.length) :
    (∀ x ∈ (mrun P X.V h (ksOf P X O h)).ctl, BB P X O h x) ∧
      (∀ e ∈ (mrun P X.V h (ksOf P X O h)).evs, ∀ x ∈ e.adep, BB P X O h x) := by
  obtain ⟨hlen, hmin⟩ := ksOf_spec H h
  have hw := mrun_wf P X.V h (ksOf P X O h)
  -- a load `x` below anchor `z` with `x ≤ z.2`, ordered before `z` when `z` is a store
  have hB : ∀ x z, z ∈ Al P X O → z.1 = h → x < z.2 → (X.evs P).isMem (h, x) →
      ((X.evs P).isSt z → (X.evs P).gmo (h, x) z) → BB P X O h x := by
    intro x z hz h1 h2 hxm hord
    refine ⟨?_, ?_⟩
    · rcases (Al_mem H hz).2 with hO | ⟨hG, hS⟩
      · exact Pl_Gl H ((mem_Pl _).2 ⟨z, hO, h1.symm, by simp only; omega⟩) hxm
      · exact Gl_down H hG (hord hS)
    · exact (lt_cutOf _ h x).2 ⟨z, hz, h1, by omega⟩
  refine ⟨fun x hx => ?_, fun e he x hx => ?_⟩
  · -- the control taint: the last step emitted the last anchor, whose control dependencies it is
    have hpos : 0 < cut P X O h := by
      rcases Nat.eq_zero_or_pos (cut P X O h) with h0 | h0
      · exfalso
        have hk0 : ksOf P X O h = 0 := by
          rcases Nat.eq_zero_or_pos (ksOf P X O h) with h1 | h1
          · exact h1
          · have := hmin 0 h1; omega
        rw [hk0] at hx; simp [mrun, MProg.init] at hx
      · exact h0
    obtain ⟨z, hz, hz1, hz2⟩ := cutOf_max _ h hpos
    obtain ⟨k, hk⟩ : ∃ k, ksOf P X O h = k + 1 := by
      rcases Nat.eq_zero_or_pos (ksOf P X O h) with h1 | h1
      · rw [h1] at hlen; simp [mrun, MProg.init] at hlen; omega
      · exact ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
    rw [hk] at hlen hx
    have hlk := hmin k (by omega)
    have hls := mrun_len_succ P X.V h k
    have hl1 : (mrun P X.V h k).evs.length = cut P X O h - 1 := by omega
    have hctl := mstep_ctl_emit P X.V h (mrun P X.V h k) (by show (mrun P X.V h (k + 1)).evs.length = _; omega)
    change x ∈ (mstep P X.V h (mrun P X.V h k)).ctl at hx
    rw [hctl] at hx
    rcases mstep_evs P X.V h (mrun P X.V h k) with he | ⟨e, he, hcd⟩
    · exfalso; have := congrArg List.length he; change (mrun P X.V h (k + 1)).evs.length = _ at this; omega
    · -- `e` is the anchor `z`
      have hzi : z.2 = (mrun P X.V h k).evs.length := by unfold cut at hl1; omega
      have hzh : z = (h, z.2) := by obtain ⟨a, b⟩ := z; simp only at hz1 ⊢; rw [hz1]
      have hzev : (X.evs P).ev z = e := by
        rw [hzh]
        exact xev_of (k := k + 1) (by change (mstep P X.V h (mrun P X.V h k)).evs[z.2]? = some e; rw [he, hzi]; simp)
      have hzm := (Al_mem H hz).1
      have hek : e.kind = .ld ∨ e.kind = .st := by rw [← hzev]; exact hzm.2
      rw [← hcd hek] at hx
      have hxl := (mrun_wf P X.V h k).ctl x (by rw [← hcd hek]; exact hx)
      have hxlt := ldAt_lt hxl
      obtain ⟨hxm, _⟩ := xld (k := k) hh hxl
      refine hB x z hz hz1 (by omega) hxm (fun hS => ?_)
      rw [hzh] at hS hzm ⊢
      exact ppoX H.ex hxm hzm (xpo (by omega) hzm.1)
        (.inr (.inr (.inr (.inr (.inr (.inl ⟨hS, rfl, by rw [← hzh, hzev]; exact hx⟩))))))
  · -- an address dependency of an event below an anchor
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hd := hw.deps i _ (List.getElem?_eq_getElem hi) x (.inl hx)
    obtain ⟨hxm, _⟩ := xld hh hd.2
    have hil : i < cut P X O h := by rw [← hlen]; exact hi
    obtain ⟨z, hz, hz1, hz2⟩ := anchor_of H hil
    have hzm := (Al_mem H hz).1
    have hzh : z = (h, z.2) := by obtain ⟨a, b⟩ := z; simp only at hz1 ⊢; rw [hz1]
    have hev : (X.evs P).ev (h, i) = (mrun P X.V h (ksOf P X O h)).evs[i] := xev hi
    refine hB x z hz hz1 (by omega) hxm (fun hS => ?_)
    rw [hzh] at hS hzm ⊢
    rcases Nat.lt_or_eq_of_le hz2 with hlt | heq
    · -- rule 13 through the event `(h, i)` (a load or a store: it has an address)
      have him : (X.evs P).isMem (h, i) := by
        refine ⟨⟨hh, _, hi⟩, ?_⟩
        unfold MEvs.isLd MEvs.isSt; rw [hev]
        cases hk : (mrun P X.V h (ksOf P X O h)).evs[i].kind with
        | ld => exact .inl rfl
        | st => exact .inr rfl
        | fence f =>
          exfalso
          rw [(mrun_new P X.V h _ i _ (List.getElem?_eq_getElem hi)).2 f hk] at hx; cases hx
      exact ppoX H.ex hxm hzm (xpo (by omega) hzm.1)
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hS, (h, i), him, xpo hd.1 him.1, xpo hlt hzm.1,
          by rw [hev]; exact hx⟩)))))))
    · -- rule 9: `z` itself
      have hz' : z.2 = i := heq.symm
      exact ppoX H.ex hxm hzm (xpo (by omega) hzm.1)
        (.inr (.inr (.inr (.inl ⟨rfl, by rw [hz', hev]; exact hx⟩))))

end lemmas

end

end Weak.Mini.Pfx
