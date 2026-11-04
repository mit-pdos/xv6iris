/-
Weak/Prom: **S3d — gmo of an infinite execution is a ranking** (plan rev 7 §8 S3d).  From `gmoOk` (a strict total
order of the memory operations) and the PROGRESS AXIOM (rvwmo.adoc:350–351 "No memory operation may be preceded in
the global memory order by an infinite sequence of other memory operations", `progressAxI`):
* `preds_finite` — every memory operation has finitely many gmo-predecessors (else an injective sequence of them);
* `rk` — the number of gmo-predecessors; `gmo_iff_rk`: on memory operations, `gmo a b ↔ rk a < rk b`;
* `rfI_unique` — the load value axiom's store is unique.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxSym

noncomputable section

namespace Weak.Prom.Pfx

open Classical
open Weak.Prom.Ref

/-- Duplicate-free copy of a list. -/
def ndL : List EvId → List EvId
  | [] => []
  | a :: t => if a ∈ ndL t then ndL t else a :: ndL t

theorem mem_ndL : ∀ (l : List EvId) (a : EvId), a ∈ ndL l ↔ a ∈ l
  | [], a => by simp [ndL]
  | b :: t, a => by
    unfold ndL
    split
    · rename_i hb
      rw [mem_ndL t a, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact (mem_ndL t a).1 hb
        · exact h
    · rw [List.mem_cons, mem_ndL t a, List.mem_cons]

theorem nodup_ndL : ∀ (l : List EvId), (ndL l).Nodup
  | [] => List.nodup_nil
  | b :: t => by
    unfold ndL
    split
    · exact nodup_ndL t
    · rename_i hb
      exact List.nodup_cons.2 ⟨hb, nodup_ndL t⟩

namespace IExec

variable {E : IExec}

theorem gmo_mem (hg : E.gmoOk) {a b : EvId} (h : E.gmo a b) : E.isMem a ∧ E.isMem b := hg.1 a b h
theorem gmo_irrefl (hg : E.gmoOk) (a : EvId) : ¬ E.gmo a a := hg.2.1 a
theorem gmo_trans (hg : E.gmoOk) {a b c : EvId} (h1 : E.gmo a b) (h2 : E.gmo b c) : E.gmo a c :=
  hg.2.2.1 a b c h1 h2
theorem gmo_asymm (hg : E.gmoOk) {a b : EvId} (h : E.gmo a b) : ¬ E.gmo b a :=
  fun h' => gmo_irrefl hg a (gmo_trans hg h h')
theorem gmo_total (hg : E.gmoOk) {a b : EvId} (ha : E.isMem a) (hb : E.isMem b) (hne : a ≠ b) :
    E.gmo a b ∨ E.gmo b a := hg.2.2.2 a b ha hb hne

/-- **Every memory operation has finitely many gmo-predecessors** (the progress axiom). -/
theorem preds_finite (hp : E.progressAxI) {e : EvId} (he : E.isMem e) : ∃ L : List EvId, ∀ a, E.gmo a e → a ∈ L := by
  apply Classical.byContradiction
  intro hne
  have H : ∀ L : List EvId, ∃ a, E.gmo a e ∧ a ∉ L := by
    intro L
    apply Classical.byContradiction
    intro h2
    apply hne
    refine ⟨L, fun a ha => ?_⟩
    apply Classical.byContradiction
    intro h3
    exact h2 ⟨a, ha, h3⟩
  let g : Nat → List EvId := fun n => Nat.rec [] (fun _ l => l ++ [Classical.choose (H l)]) n
  let f : Nat → EvId := fun n => Classical.choose (H (g n))
  have hgs : ∀ n, g (n + 1) = g n ++ [f n] := fun n => rfl
  have hg : ∀ n m, m < n → f m ∈ g n := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      rw [hgs]
      rcases Nat.lt_or_ge m n with h1 | h1
      · exact List.mem_append_left _ (ih m h1)
      · have : m = n := by omega
        subst this
        exact List.mem_append_right _ (List.mem_singleton_self _)
  have hnot : ∀ n, f n ∉ g n := fun n => (Classical.choose_spec (H (g n))).2
  refine hp e he ⟨f, fun n m hnm => ?_, fun n => (Classical.choose_spec (H (g n))).1⟩
  rcases Nat.lt_trichotomy n m with h1 | h1 | h1
  · exact absurd (hnm ▸ hg m n h1) (hnot m)
  · exact h1
  · exact absurd (hnm.symm ▸ hg n m h1) (hnot n)

/-- The gmo-predecessors of `e` (a duplicate-free list; empty if there is no finite superset). -/
def preds (E : IExec) (e : EvId) : List EvId :=
  if h : ∃ L : List EvId, ∀ a, E.gmo a e → a ∈ L then (ndL (Classical.choose h)).filter (fun a => decide (E.gmo a e))
  else []

theorem mem_preds (hp : E.progressAxI) {e : EvId} (he : E.isMem e) (a : EvId) : a ∈ E.preds e ↔ E.gmo a e := by
  have h := preds_finite hp he
  unfold preds
  rw [dif_pos h, List.mem_filter, mem_ndL, decide_eq_true_eq]
  exact ⟨fun h1 => h1.2, fun h1 => ⟨Classical.choose_spec h a h1, h1⟩⟩

theorem nodup_preds (e : EvId) : (E.preds e).Nodup := by
  unfold preds
  split
  · exact (nodup_ndL _).filter _
  · exact List.nodup_nil

/-- THE RANK of a memory operation: its number of gmo-predecessors. -/
def rk (E : IExec) (e : EvId) : Nat := (E.preds e).length

theorem rk_lt (hg : E.gmoOk) (hp : E.progressAxI) {a b : EvId} (h : E.gmo a b) : E.rk a < E.rk b := by
  obtain ⟨ha, hb⟩ := gmo_mem hg h
  have hnd : (a :: E.preds a).Nodup :=
    List.nodup_cons.2 ⟨fun hm => gmo_irrefl hg a ((mem_preds hp ha a).1 hm), nodup_preds a⟩
  have hsub : ∀ x ∈ a :: E.preds a, x ∈ E.preds b := by
    intro x hx
    rw [mem_preds hp hb]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h
    · exact gmo_trans hg ((mem_preds hp ha x).1 hx) h
  have := nodup_length_le _ _ hnd hsub
  simp only [List.length_cons] at this
  unfold rk; omega

/-- On memory operations, gmo IS the rank order. -/
theorem gmo_iff_rk (hg : E.gmoOk) (hp : E.progressAxI) {a b : EvId} (ha : E.isMem a) (hb : E.isMem b) :
    E.gmo a b ↔ E.rk a < E.rk b := by
  refine ⟨rk_lt hg hp, fun h => ?_⟩
  by_cases hab : a = b
  · subst hab; omega
  · rcases gmo_total hg ha hb hab with h1 | h1
    · exact h1
    · have := rk_lt hg hp h1; omega

theorem rk_inj (hg : E.gmoOk) (hp : E.progressAxI) {a b : EvId} (ha : E.isMem a) (hb : E.isMem b)
    (h : E.rk a = E.rk b) : a = b := by
  apply Classical.byContradiction
  intro hab
  rcases gmo_total hg ha hb hab with h1 | h1
  · have := rk_lt hg hp h1; omega
  · have := rk_lt hg hp h1; omega

/-- The load value axiom's store is unique. -/
theorem rfI_unique (hg : E.gmoOk) {r : EvId} {x : Nat} :
    ∀ {o o' : Option EvId}, E.rfI r x o → E.rfI r x o' → o = o'
  | none, none, _, _ => rfl
  | none, some w, h1, h2 => absurd h2.1 (h1 w)
  | some w, none, h1, h2 => absurd h1.1 (h2 w)
  | some w, some w', h1, h2 => by
    rcases h1.2 w' h2.1 with h | h
    · rw [h]
    · rcases h2.2 w h1.1 with h' | h'
      · rw [h']
      · exact absurd (gmo_trans hg h h') (gmo_irrefl hg w')

end IExec

end Weak.Prom.Pfx

end
