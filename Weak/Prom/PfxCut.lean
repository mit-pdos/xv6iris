/-
Weak/Prom: **S3d — the cut** (plan rev 7 §6 S3d: "re-source 'late' reads whose values feed nothing earlier in gmo,
bounded by the progress axiom").  Given an infinite execution `E` and a finite list `O` of its memory operations:
* `Pl` = po-down(O) (every event of a hart up to an observed one), `Ml` its memory operations, `Gl` the
  gmo-down-closure of `Ml` (FINITE by progress: `Ml`'s elements and their gmo-predecessors, PfxRank.lean), `Sl` the
  stores of `Gl`, `Al = O ++ Sl` the ANCHORS;
* `cut h` = one past hart `h`'s last anchor; `D` = every event of hart `h` below `cut h` (`inD`), a po-prefix;
* `deps_G` — THE KEY BOUND: every address or control dependency of an event of `D` is in `Gl`: below an observed
  anchor it is in po-down(O); below a store anchor `z` it is ordered before `z` by rule 11 (control: z's control
  dependencies contain every earlier event's), rule 9 (z's own address) or rule 13 (an address dependency of an
  earlier memory operation), rvwmo.adoc:293–302;
* `trsC` — hart `h` stopped right after its last anchor (`kcut`): its path conditions only mention loads of `Gl`
  (`cutP_exists`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxRank

noncomputable section

namespace Weak.Prom.Pfx

open Classical
open Weak.Prom.Ref
open Weak.Prom.Cmp (depsOf)

/-- The hypotheses: an infinite execution of an S3a-scope program without I/O, and observed memory operations. -/
structure Hyp (E : IExec) (O : List EvId) : Prop where
  conf : E.conforms
  conds : E.condsOkI
  ref : E.rvwmoRefInf
  frag : FragT E.T
  io : E.T.io = []
  obs : ∀ e ∈ O, E.isMem e

/-- One past the last element of `A` on hart `h`. -/
def cutOf (A : List EvId) (h : Nat) : Nat := A.foldr (fun z c => if z.1 = h then max c (z.2 + 1) else c) 0

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

namespace Cut

variable (E : IExec) (O : List EvId)

/-- po-down(O). -/
def Pl : List EvId := O.flatMap (fun o => (List.range (o.2 + 1)).map (fun i => (o.1, i)))

/-- Its memory operations. -/
def Ml : List EvId := (Pl O).filter (fun e => decide (E.isMem e))

/-- Their gmo-down-closure (finite: progress). -/
def Gl : List EvId := (Ml E O).flatMap (fun m => m :: E.preds m)

/-- The stores of `Gl`. -/
def Sl : List EvId := (Gl E O).filter (fun e => (E.sk e).kind.isStore)

/-- The anchors. -/
def Al : List EvId := O ++ Sl E O

/-- The cut of hart `h`. -/
def cut (h : Nat) : Nat := cutOf (Al E O) h

/-- The cut state of hart `h`: exactly `cut h` events, path conditions over loads of `Gl`. -/
def CutP (h k : Nat) : Prop :=
  (E.st h k).evs.length = cut E O h ∧ ∀ c ∈ (E.st h k).conds, ∀ x ∈ c.2.1.vars ++ c.2.2.1.vars, x ∈ Gl E O

def kcut (h : Nat) : Nat := if hk : ∃ k, CutP E O h k then Classical.choose hk else 0

/-- **THE FINITE PARTIAL EXECUTION's states**: every hart stopped at its cut. -/
def trsC : List SSt := (List.range E.T.harts.length).map (fun h => E.st h (kcut E O h))

end Cut

open Cut

section lemmas

variable {E : IExec} {O : List EvId} (H : Hyp E O)
include H

theorem H_gmo : E.gmoOk := H.ref.1
theorem H_prog : E.progressAxI := H.ref.2.2.2.2.2.2
theorem H_ppo {a b : EvId} (h : E.ppoI a b) : E.gmo a b := H.ref.2.2.1 a b (Or.inl h)

theorem mem_Pl (e : EvId) : e ∈ Pl O ↔ ∃ o ∈ O, e.1 = o.1 ∧ e.2 ≤ o.2 := by
  unfold Pl
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨o, ho, i, hi, rfl⟩; exact ⟨o, ho, rfl, by simp; omega⟩
  · rintro ⟨o, ho, h1, h2⟩; exact ⟨o, ho, e.2, by omega, by rw [← h1]⟩

theorem mem_Gl (e : EvId) : e ∈ Gl E O ↔ ∃ m ∈ Ml E O, e = m ∨ E.gmo e m := by
  unfold Gl
  simp only [List.mem_flatMap, List.mem_cons]
  constructor
  · rintro ⟨m, hm, h1 | h1⟩
    · exact ⟨m, hm, Or.inl h1⟩
    · have hmm : E.isMem m := by unfold Ml at hm; simpa using (List.mem_filter.1 hm).2
      exact ⟨m, hm, Or.inr ((IExec.mem_preds (H_prog H) hmm e).1 h1)⟩
  · rintro ⟨m, hm, h1 | h1⟩
    · exact ⟨m, hm, Or.inl h1⟩
    · have hmm : E.isMem m := by unfold Ml at hm; simpa using (List.mem_filter.1 hm).2
      exact ⟨m, hm, Or.inr ((IExec.mem_preds (H_prog H) hmm e).2 h1)⟩

theorem Gl_down {a e : EvId} (he : e ∈ Gl E O) (h : E.gmo a e) : a ∈ Gl E O := by
  obtain ⟨m, hm, h1 | h1⟩ := (mem_Gl H e).1 he
  · exact (mem_Gl H a).2 ⟨m, hm, Or.inr (h1 ▸ h)⟩
  · exact (mem_Gl H a).2 ⟨m, hm, Or.inr (IExec.gmo_trans (H_gmo H) h h1)⟩

theorem Gl_mem {e : EvId} (he : e ∈ Gl E O) : E.isMem e := by
  obtain ⟨m, hm, h1 | h1⟩ := (mem_Gl H e).1 he
  · unfold Ml at hm; subst h1; simpa using (List.mem_filter.1 hm).2
  · exact (IExec.gmo_mem (H_gmo H) h1).1

theorem Pl_Gl {e : EvId} (hp : e ∈ Pl O) (hm : E.isMem e) : e ∈ Gl E O :=
  (mem_Gl H e).2 ⟨e, List.mem_filter.2 ⟨hp, by simpa using hm⟩, Or.inl rfl⟩

theorem Al_mem {z : EvId} (hz : z ∈ Al E O) : E.isMem z := by
  rcases List.mem_append.1 hz with hz | hz
  · exact H.obs z hz
  · exact Gl_mem H (List.mem_filter.1 hz).1

theorem hart_lt {e : EvId} (he : E.has e) : e.1 < E.T.harts.length := he.1

/-- Membership in the cut. -/
def inD (E : IExec) (O : List EvId) (e : EvId) : Prop := e.1 < E.T.harts.length ∧ e.2 < cut E O e.1

theorem inD_has {e : EvId} (he : inD E O e) : E.has e := by
  obtain ⟨z, hz, h1, h2⟩ := (lt_cutOf _ _ _).1 he.2
  have hzm := Al_mem H hz
  have := has_of_lt H.conf H.frag he.1 (h1 ▸ hzm.1 : E.has (e.1, z.2)) h2
  exact this

theorem inD_anchor {e : EvId} (he : inD E O e) : ∃ z ∈ Al E O, z.1 = e.1 ∧ e.2 ≤ z.2 :=
  (lt_cutOf _ _ _).1 he.2

theorem inD_of_le {e : EvId} (he : inD E O e) {i : Nat} (hi : i ≤ e.2) : inD E O (e.1, i) :=
  ⟨he.1, by have := he.2; simp only; omega⟩

theorem Al_inD {z : EvId} (hz : z ∈ Al E O) : inD E O z :=
  ⟨(Al_mem H hz).1.1, (lt_cutOf _ _ _).2 ⟨z, hz, rfl, Nat.le_refl _⟩⟩

/-- **THE KEY BOUND**: every address or control dependency of an event of the cut is in `Gl`. -/
theorem deps_G {e : EvId} (he : inD E O e) {d : Nat}
    (hd : d ∈ (E.sk e).adep ∨ d ∈ (E.sk e).cdep) : (e.1, d) ∈ Gl E O := by
  obtain ⟨h, i⟩ := e
  have hhas := inD_has H he
  have hh : h < E.T.harts.length := he.1
  have hdm : depsOf (E.sk (h, i)) d := by rcases hd with hd | hd; exact Or.inl hd; exact Or.inr (Or.inr hd)
  obtain ⟨hdi, hdmem⟩ := deps_mem H.conf H.frag hh hhas hdm
  obtain ⟨z, hz, hz1, hz2⟩ := inD_anchor H he
  simp only at hz1 hz2
  rcases List.mem_append.1 hz with hzo | hzs
  · exact Pl_Gl H ((mem_Pl H (h, d)).2 ⟨z, hzo, hz1.symm, by simp; omega⟩) hdmem
  · obtain ⟨hzg, hzst⟩ := List.mem_filter.1 hzs
    have hzm := Gl_mem H hzg
    obtain ⟨z1, z2⟩ := z
    simp only at hz1 hz2; subst z1
    have hpo : poS E.sk (h, d) (h, z2) = true :=
      idx_po H.conf H.frag hh hzm.1 (by omega) hdmem.2
    suffices hg : E.gmo (h, d) (h, z2) from Gl_down H hzg hg
    apply H_ppo H
    refine ⟨hdmem, hzm, hpo, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    rcases hd with hd | hd
    · rcases Nat.eq_or_lt_of_le hz2 with hiz | hiz
      · subst hiz
        right; right; right; right; right; left
        simp only [rule9, beq_self_eq_true, Bool.true_and, List.contains_iff_mem]
        exact hd
      · right; right; right; right; right; right; right; right
        have hem : (E.sk (h, i)).kind.isMem = true := by
          rcases fragEv H.conf H.frag hh hhas with hk | hk | ⟨f, hk, ha, _⟩
          · change (E.sev (h, i)).sk.kind.isMem = true; rw [hk]; rfl
          · change (E.sev (h, i)).sk.kind.isMem = true; rw [hk]; rfl
          · exfalso; change d ∈ (E.sev (h, i)).sk.adep at hd; rw [ha] at hd; simp at hd
        refine ⟨by simpa using hzst, (h, i), hhas, hem, idx_po H.conf H.frag hh hhas hdi hdmem.2,
          idx_po H.conf H.frag hh hzm.1 hiz hem, by simpa using hd⟩
    · have hdz : d ∈ (E.sk (h, z2)).cdep := by
        rcases Nat.eq_or_lt_of_le hz2 with hiz | hiz
        · subst hiz; exact hd
        · exact cdep_mono H.conf H.frag hh hzm.1 hiz hzm.2 hd
      right; right; right; right; right; right; right; left
      simp only [rule11, beq_self_eq_true, Bool.and_true, Bool.and_eq_true, List.contains_iff_mem]
      exact ⟨by simpa using hzst, hdz⟩

/-- The cut state exists. -/
theorem cutP_exists {h : Nat} (hh : h < E.T.harts.length) : ∃ k, CutP E O h k := by
  by_cases hc : cut E O h = 0
  · refine ⟨0, ?_, fun c hcc => ?_⟩
    · rw [hc, (H.conf h hh).1]; rfl
    · rw [(H.conf h hh).1] at hcc; simp [Test.init] at hcc
  · obtain ⟨z, hz, hz1, hz2⟩ := cutOf_max (Al E O) h (Nat.pos_of_ne_zero hc)
    have hzm := Al_mem H hz
    obtain ⟨z1, z2⟩ := z
    simp only at hz1 hz2; subst z1
    obtain ⟨k, hk1, hk2⟩ := cut_conds H.conf H.frag hh hzm.1 hzm.2
    refine ⟨k, by rw [hk1]; exact hz2, fun c hcc x hx => ?_⟩
    obtain ⟨hx1, hx2⟩ := hk2 c hcc x hx
    have := deps_G H (Al_inD H hz) (d := x.2) (Or.inr hx2)
    obtain ⟨x1, x2⟩ := x
    simp only at hx1; subst x1; exact this

theorem kcut_spec {h : Nat} (hh : h < E.T.harts.length) : CutP E O h (kcut E O h) := by
  have he := cutP_exists H hh
  unfold kcut; rw [dif_pos he]; exact Classical.choose_spec he

theorem trsC_len : (trsC E O).length = E.T.harts.length := by simp [trsC]

theorem trsC_get {h : Nat} (hh : h < E.T.harts.length) : (trsC E O)[h]? = some (E.st h (kcut E O h)) := by
  simp [trsC, List.getElem?_map, List.getElem?_range hh]

theorem mem_sidsC (e : EvId) : e ∈ sids (trsC E O) ↔ inD E O e := by
  unfold sids
  rw [mem_idsOf]
  constructor
  · rintro ⟨l, hl, hi⟩
    simp only [List.getElem?_map] at hl
    have hh : e.1 < E.T.harts.length := by
      rcases Nat.lt_or_ge e.1 E.T.harts.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none (by rw [trsC_len H]; exact h1)] at hl; cases hl
    rw [trsC_get H hh] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    exact ⟨hh, by rw [← (kcut_spec H hh).1]; exact hi⟩
  · rintro ⟨hh, hi⟩
    refine ⟨(E.st e.1 (kcut E O e.1)).evs, by simp [List.getElem?_map, trsC_get H hh], ?_⟩
    rw [(kcut_spec H hh).1]; exact hi

theorem sevAt_C {e : EvId} (he : inD E O e) : sevAt (trsC E O) e = E.sev e := by
  unfold sevAt
  rw [trsC_get H he.1]
  simp only [Option.bind_some]
  have hl : e.2 < (E.st e.1 (kcut E O e.1)).evs.length := by rw [(kcut_spec H he.1).1]; exact he.2
  rw [sev_eq H.conf H.frag he.1 hl]
  rfl

theorem concC_ev (μ : Val) (g : List EvId) {e : EvId} (he : inD E O e) :
    (conc E.T (trsC E O) μ g).ev e = concEv μ e.1 e.2 (E.sev e) := by
  rw [conc_ev _ _ _ _ _ ((mem_sidsC H e).2 he), sevAt_C H he]

theorem concC_sk (μ : Val) (g : List EvId) {e : EvId} (he : inD E O e) :
    (conc E.T (trsC E O) μ g).sk e = E.sk e := by
  unfold Exec.sk; rw [concC_ev H μ g he]; rfl

/-- A valuation that agrees with `E`'s on `Gl` gives every event of the cut `E`'s address. -/
def AgreeG (E : IExec) (O : List EvId) (μ : Val) : Prop := ∀ x ∈ Gl E O, μ x = E.ν x

theorem concC_pa {μ : Val} (hμ : AgreeG E O μ) (g : List EvId) {e : EvId} (he : inD E O e) :
    ((conc E.T (trsC E O) μ g).ev e).pa = (E.ev e).pa := by
  rw [concC_ev H μ g he]
  show (E.sev e).addr.eval μ = (E.sev e).addr.eval E.ν
  apply Ex.eval_congr
  intro v hv
  obtain ⟨h, i⟩ := e
  obtain ⟨hv1, hv2⟩ := addr_vars H.conf H.frag he.1 (inD_has H he) hv
  apply hμ
  have := deps_G H he (d := v.2) (Or.inl hv2)
  obtain ⟨v1, v2⟩ := v
  simp only at hv1; subst v1; exact this

end lemmas

end Weak.Prom.Pfx

end
